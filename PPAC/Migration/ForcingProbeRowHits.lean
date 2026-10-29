/- Pinned CodeCardinals.ordinalType_lower_count:196-218 (hdisj and hits).
Direct main consumer: ConcreteQuotients.code_ordinalType_cardinal:302.
Actual outside-copy conditions and per-row strengthening; no generic-filter
selection or the separate classFiber_dense_lower branch. -/
import PPAC.Migration.ForcingProbeDensity
import PPAC.Migration.ForcingOutsideCopies

namespace PPAC.Migration.ForcingProbeRowHits
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ForcingCohenCoordinates (Cartesian)
open ForcingCohenConditions (Condition Carrier)
open ForcingConditionGraphs (FunctionOn)
open ForcingSupportSize (MapsTo Injection Small)
open ConstructionCohenCompatibility (Compatible Restricted)
open ForcingProbeDensity (Copies DisjointOff)
open ForcingPowerName (Subset)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 3000000
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def Value (F i j d : M.Carrier .set) : Prop :=
  ∃ z, PureKuratowski.Code M z i j ∧ PureKuratowski.PairMember M z d F

def value {n : Nat} (F i j d : Fin n) : Project.Formula 1 n :=
  .existsE (.conj (ProjectSyntax.encode id (PairSyntax.ordered 0 i.succ j.succ))
    (ProjectSyntax.encode id (Source.SetLanguage.edge F.succ 0 d.succ)))

theorem value_freeClosed {n : Nat} (F i j d : Fin n) : (value F i j d).FreeClosed := by
  simp -implicitDefEqProofs [value,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed]

theorem value_semantics (hM : FirstOrder.Theory.Models M nativeZF) {n : Nat}
    (env : Env (Project.FirstOrderSemantics.reduct M) n) (F i j d : Fin n) :
    Project.Formula.satisfies env (value F i j d) ↔ Value (env.bound F) (env.bound i) (env.bound j) (env.bound d) := by
  simp only [value,Value,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_code,KuratowskiZF.source_edge]
  rfl

theorem row_function (hM : FirstOrder.Theory.Models M nativeZF)
    {A P F S w J root X i : M.Carrier .set} (hP : Cartesian A A P) (hF : Copies P F S w J root)
    (hX : Carrier S w X) (hi : (Project.FirstOrderSemantics.reduct M).mem i A) :
    ∃ row, Copies A row S w J root ∧ ∀ j d, PureKuratowski.PairMember M j d row ↔
      (Project.FirstOrderSemantics.reduct M).mem j A ∧ Value F i j d := by
  let schema : Project.BinarySchema 2 := {body := value 2 3 1 0,freeClosed := value_freeClosed _ _ _ _}
  let env : Env (Project.FirstOrderSemantics.reduct M) 2 := ⟨Source.SetLanguage.args2 F i,fun _ => A⟩
  have hs j d : schema.denote env j d ↔ Value F i j d := by
    simp only [schema,Project.BinarySchema.denote,value_semantics hM]; rfl
  obtain ⟨row,hr,he⟩ := ZF.exists_setFunctionFromTo_of_denote (ModelTransfer.project_models_iff.mp hM)
    (KuratowskiZF.interpretation hM) schema env (source := A) (target := X) (by
      intro j hj
      obtain ⟨z,hz⟩ := KuratowskiZF.exists_code hM i j
      obtain ⟨d,hd,_⟩ := hF.1.2 z ((hP z).mpr ⟨i,hi,j,hj,hz⟩)
      exact ⟨d,(hs j d).mpr ⟨z,hz,hd⟩⟩) (by
      intro j _ d e hd he
      obtain ⟨z,hz,hd⟩ := (hs j d).mp hd
      obtain ⟨z',hz',he⟩ := (hs j e).mp he
      have eq := KuratowskiZF.code_unique hM hz hz'
      subst z'
      exact ForcingConditionGraphs.function_unique hF.1 hd he) (by
      intro j d _ hd
      obtain ⟨z,_,hd⟩ := (hs j d).mp hd
      exact (hX d).mpr (hF.2 z d hd).1)
  have hExact j d := (he j d).trans (and_congr Iff.rfl (hs j d))
  refine ⟨row,⟨((ForcingSupportSize.native_mapsTo hM _ _ _).mpr hr).1,?_⟩,hExact⟩
  intro j d hd
  obtain ⟨_,z,_,hd⟩ := (hExact j d).mp hd
  exact hF.2 z d hd

def ConditionAt (copies i d : M.Carrier .set) : Prop :=
  ∃ record name, PureKuratowski.PairMember M i record copies ∧ PureKuratowski.Code M record d name

def conditionAt {n : Nat} (copies i d : Fin n) : Project.Formula 1 n :=
  .existsE (.existsE (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge copies.succ.succ i.succ.succ 1))
    (ProjectSyntax.encode id (PairSyntax.ordered 1 d.succ.succ 0))))

theorem conditionAt_freeClosed {n : Nat} (copies i d : Fin n) : (conditionAt copies i d).FreeClosed := by
  simp -implicitDefEqProofs [conditionAt,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed]

theorem conditionAt_semantics (hM : FirstOrder.Theory.Models M nativeZF) {n : Nat}
    (env : Env (Project.FirstOrderSemantics.reduct M) n) (copies i d : Fin n) :
    Project.Formula.satisfies env (conditionAt copies i d) ↔ ConditionAt (env.bound copies) (env.bound i) (env.bound d) := by
  simp only [conditionAt,ConditionAt,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_code,KuratowskiZF.source_edge]
  rfl


theorem condition_projection (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    {R : Source.Formula (k+2)} {Hdom : Source.Formula (k+1)} {env : Fin k → M.Carrier .set}
    {v : Fin 7 → M.Carrier .set} {G SF w bound labels E J delta list P targets copies X : M.Carrier .set}
    (hCopies : ForcingOutsideCopies.Family R Hdom env v G SF w bound labels E J delta list P targets copies)
    (hX : Carrier (v 2) w X) :
    ∃ conditions, Copies P conditions (v 2) w J delta ∧ ∀ i d, PureKuratowski.PairMember M i d conditions ↔
      (Project.FirstOrderSemantics.reduct M).mem i P ∧ ConditionAt copies i d := by
  let schema : Project.BinarySchema 1 := {body := conditionAt 2 1 0,freeClosed := conditionAt_freeClosed _ _ _}
  let penv : Env (Project.FirstOrderSemantics.reduct M) 1 := ⟨fun _ => copies,fun _ => X⟩
  have hs i d : schema.denote penv i d ↔ ConditionAt copies i d := by
    simp only [schema,Project.BinarySchema.denote,conditionAt_semantics hM]; rfl
  have data i d (hd : ConditionAt copies i d) : Condition (v 2) w d ∧ Restricted J d delta := by
    obtain ⟨record,name,hi,hRec⟩ := hd
    obtain ⟨_,_,d',name',_,_,_,hRec',hd',_,hRestr,_⟩ := hCopies.2 i record hi
    obtain ⟨rfl,rfl⟩ := PureKuratowski.code_injective hRec hRec'
    exact ⟨hd',hRestr⟩
  obtain ⟨conditions,hF,hExact⟩ := ZF.exists_setFunctionFromTo_of_denote (ModelTransfer.project_models_iff.mp hM)
    (KuratowskiZF.interpretation hM) schema penv (source := P) (target := X) (by
      intro i hi
      obtain ⟨record,hir,_⟩ := hCopies.1.2 i hi
      obtain ⟨_,_,d,name,_,_,_,hRec,_⟩ := hCopies.2 i record hir
      exact ⟨d,(hs i d).mpr ⟨record,name,hir,hRec⟩⟩) (by
      intro i _ d e hd he
      obtain ⟨record,name,hi,hRec⟩ := (hs i d).mp hd
      obtain ⟨record',name',hi',hRec'⟩ := (hs i e).mp he
      have eq := ForcingConditionGraphs.function_unique hCopies.1 hi hi'
      subst record'
      exact (PureKuratowski.code_injective hRec hRec').1) (by
      intro i d _ hd
      exact (hX d).mpr (data i d ((hs i d).mp hd)).1)
  have he i d := (hExact i d).trans (and_congr Iff.rfl (hs i d))
  exact ⟨conditions,⟨((ForcingSupportSize.native_mapsTo hM _ _ _).mpr hF).1,
    fun i d hd => data i d ((he i d).mp hd).2⟩,he⟩


theorem conditions_disjoint {k : Nat}
    {R : Source.Formula (k+2)} {Hdom : Source.Formula (k+1)} {env : Fin k → M.Carrier .set}
    {v : Fin 7 → M.Carrier .set} {G SF w bound labels E J delta list P targets copies conditions I mul r b p t multipliers : M.Carrier .set}
    (hCopies : ForcingOutsideCopies.Family R Hdom env v G SF w bound labels E J delta list P targets copies)
    (hTargets : ForcingOutsideCopies.Targets (v 0) I mul r b p P multipliers targets)
    (hProjection : ∀ i d, PureKuratowski.PairMember M i d conditions ↔ (Project.FirstOrderSemantics.reduct M).mem i P ∧ ConditionAt copies i d)
    (hr : Injection (v 0) I r) (hSub : ForcingDiagramOrder.Sub (v 0) mul r t p)
    (hRange : ForcingSupportedNames.Range (v 0) p J)
    (hIndependent : ∀ i j m n, PureKuratowski.PairMember M i m multipliers → PureKuratowski.PairMember M j n multipliers →
      i ≠ j → ConstructionDiagramPlacements.ConeEquality (v 0) mul m n t) : DisjointOff P conditions J := by
  intro i j d e x _ _ hid hje hdx hex
  apply Classical.byContradiction
  intro hij
  obtain ⟨_,record,name,hir,hRec⟩ := (hProjection i d).mp hid
  obtain ⟨_,record',name',hjr,hRec'⟩ := (hProjection j e).mp hje
  obtain ⟨sm,hsm,d',name0,_,_,_,hRec0,_,hdSupp,_⟩ := hCopies.2 i record hir
  obtain ⟨sn,hsn,e',name1,_,_,_,hRec1,_,heSupp,_⟩ := hCopies.2 j record' hjr
  obtain ⟨rfl,rfl⟩ := PureKuratowski.code_injective hRec hRec0
  obtain ⟨rfl,rfl⟩ := PureKuratowski.code_injective hRec' hRec1
  obtain ⟨_,_,m,him,hSubm⟩ := hTargets.2 i sm hsm
  obtain ⟨_,_,n,hjn,hSubn⟩ := hTargets.2 j sn hsn
  have hInter := ConstructionDiagramPlacements.range_inter_sub hr hSubm hSubn hSub (hIndependent i j m n him hjn hij)
  obtain ⟨⟨k,val,hdx⟩,hxJ⟩ := hdx
  obtain ⟨⟨l,val',hex⟩,_⟩ := hex
  exact hxJ ((hRange x).mpr ((hInter x).mp ⟨hdSupp x k val hdx,heSupp x l val' hex⟩))


def Projection (P copies conditions : M.Carrier .set) : Prop :=
  ∀ i d, PureKuratowski.PairMember M i d conditions ↔ (Project.FirstOrderSemantics.reduct M).mem i P ∧ ConditionAt copies i d

def projection {n : Nat} (P copies conditions : Fin n) : Project.Formula 1 n :=
  .forallE (.forallE (.iff (ProjectSyntax.encode id (Source.SetLanguage.edge conditions.succ.succ 1 0))
    (.conj (.mem (.bound 1) (.bound P.succ.succ)) (conditionAt copies.succ.succ 1 0))))

theorem projection_freeClosed {n : Nat} (P copies conditions : Fin n) : (projection P copies conditions).FreeClosed := by
  simp -implicitDefEqProofs [projection,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,conditionAt_freeClosed]

theorem projection_semantics (hM : FirstOrder.Theory.Models M nativeZF) {n : Nat}
    (env : Env (Project.FirstOrderSemantics.reduct M) n) (P copies conditions : Fin n) :
    Project.Formula.satisfies env (projection P copies conditions) ↔ Projection (env.bound P) (env.bound copies) (env.bound conditions) := by
  simp only [projection,Projection,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_iff_iff,
    Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,conditionAt_semantics hM]
  rfl


def independent {n : Nat} (D mul t multipliers : Fin n) : Project.Formula 1 n :=
  .forallE (.forallE (.forallE (.forallE (.imp
    (ProjectSyntax.encode id (Source.SetLanguage.edge multipliers.succ.succ.succ.succ 3 1))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge multipliers.succ.succ.succ.succ 2 0))
      (.imp (.neg (Project.Formula.extensionalEq (.bound 3) (.bound 2)))
        (ConstructionDiagramPlacements.coneEquality D.succ.succ.succ.succ mul.succ.succ.succ.succ 1 0 t.succ.succ.succ.succ)))))))

theorem independent_freeClosed {n : Nat} (D mul t multipliers : Fin n) : (independent D mul t multipliers).FreeClosed := by
  simp -implicitDefEqProofs [independent,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
    Project.Formula.extensionalEq,ConstructionDiagramPlacements.coneEquality_freeClosed]

theorem independent_semantics (hM : FirstOrder.Theory.Models M nativeZF) {n : Nat}
    (env : Env (Project.FirstOrderSemantics.reduct M) n) (D mul t multipliers : Fin n) :
    Project.Formula.satisfies env (independent D mul t multipliers) ↔
      ∀ i j m q, PureKuratowski.PairMember M i m (env.bound multipliers) → PureKuratowski.PairMember M j q (env.bound multipliers) →
        i ≠ j → ConstructionDiagramPlacements.ConeEquality (env.bound D) (env.bound mul) m q (env.bound t) := by
  simp only [independent,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_neg_iff,
    Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM),Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,
    ConstructionDiagramPlacements.coneEquality_semantics hM]
  rfl

theorem row_hits (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M))
    {A P F I K C B S w J root X i c : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) (hP : Cartesian A A P)
    (hC : Cartesian I K C) (hS : Cartesian C B S) (hX : Carrier S w X)
    (hF : Copies P F S w J root) (hDisj : DisjointOff P F J) (hA : ¬ Small A w)
    (hi : (Project.FirstOrderSemantics.reduct M).mem i A)
    (hc : (Project.FirstOrderSemantics.reduct M).mem c X) (hRoot : Subset root c) :
    ∃ f j d, (Project.FirstOrderSemantics.reduct M).mem f X ∧ Subset c f ∧
      (Project.FirstOrderSemantics.reduct M).mem j A ∧ Value F i j d ∧ Subset d f := by
  obtain ⟨rf,hRF,hExact⟩ := row_function hM hP hF hX hi
  have hDisjRow : DisjointOff A rf J := by
    intro j k d e x hj hk hjd hke hdx hex
    obtain ⟨_,z,hz,hzd⟩ := (hExact j d).mp hjd
    obtain ⟨_,z',hz',hze⟩ := (hExact k e).mp hke
    have eq := hDisj z z' d e x ((hP z).mpr ⟨i,hi,j,hj,hz⟩) ((hP z').mpr ⟨i,hi,k,hk,hz'⟩) hzd hze hdx hex
    subst z'
    exact (PureKuratowski.code_injective hz hz').2
  obtain ⟨f,j,d,hf,hcf,hj,hjd,hdf⟩ := ForcingProbeDensity.hits hM hChoice hw hC hS hRF hDisjRow hA ((hX c).mp hc) hRoot
  exact ⟨f,j,d,(hX f).mpr hf,hcf,hj,((hExact j d).mp hjd).2,hdf⟩

def Hits (A F X root : M.Carrier .set) : Prop :=
  ∀ i, (Project.FirstOrderSemantics.reduct M).mem i A → ∀ c,
    (Project.FirstOrderSemantics.reduct M).mem c X → Subset root c →
    ∃ f j d, (Project.FirstOrderSemantics.reduct M).mem f X ∧ Subset c f ∧
      (Project.FirstOrderSemantics.reduct M).mem j A ∧ Value F i j d ∧ Subset d f

def hits {n : Nat} (A F X root : Fin n) : Project.Formula 1 n :=
  .forallE (.imp (.mem (.bound 0) (.bound A.succ))
    (.forallE (.imp (.mem (.bound 0) (.bound X.succ.succ))
      (.imp (ProjectSyntax.encode id (Source.SetLanguage.subset root.succ.succ 0))
        (.existsE (.existsE (.existsE
          (.conj (.mem (.bound 2) (.bound X.succ.succ.succ.succ.succ))
            (.conj (ProjectSyntax.encode id (Source.SetLanguage.subset 3 2))
              (.conj (.mem (.bound 1) (.bound A.succ.succ.succ.succ.succ))
                (.conj (value F.succ.succ.succ.succ.succ 4 1 0)
                  (ProjectSyntax.encode id (Source.SetLanguage.subset 0 2)))))))))))))

theorem hits_freeClosed {n : Nat} (A F X root : Fin n) : (hits A F X root).FreeClosed := by
  simp -implicitDefEqProofs [hits,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,value_freeClosed]

theorem hits_semantics (hM : FirstOrder.Theory.Models M nativeZF) {n : Nat}
    (env : Env (Project.FirstOrderSemantics.reduct M) n) (A F X root : Fin n) :
    Project.Formula.satisfies env (hits A F X root) ↔ Hits (env.bound A) (env.bound F) (env.bound X) (env.bound root) := by
  simp only [hits,Hits,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_mem_iff,
    Project.Term.eval_bound,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingLabelPermutations.subset_semantics (M := M),value_semantics hM]
  rfl

theorem source_construct (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (G SF mul : Fin k)
    {A P I K B w bound labels E J delta list targets copies r b p t multipliers : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hp : ForcingProductFamily.Presentation (env (rho 0)) I K B w (env (rho 1)) (env (rho 2))
      (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hP : Cartesian A A P) (hA : ¬ Small A w)
    (hCopies : ForcingOutsideCopies.Family (ForcingProductSymmetry.orderFormula (rho 0) mul)
      (ForcingPairUnion.domain rho G SF) env (fun j => env (rho j)) (env G) (env SF) w bound labels E J delta list P targets copies)
    (hTargets : ForcingOutsideCopies.Targets (env (rho 0)) I (env mul) r b p P multipliers targets)
    (hr : Injection (env (rho 0)) I r) (hSub : ForcingDiagramOrder.Sub (env (rho 0)) (env mul) r t p)
    (hRange : ForcingSupportedNames.Range (env (rho 0)) p J)
    (hIndependent : ∀ i j m n, PureKuratowski.PairMember M i m multipliers → PureKuratowski.PairMember M j n multipliers →
      i ≠ j → ConstructionDiagramPlacements.ConeEquality (env (rho 0)) (env mul) m n t) :
    ∃ conditions, Copies P conditions (env (rho 2)) w J delta ∧ Projection P copies conditions ∧
      Hits A conditions (env (rho 3)) delta := by
  obtain ⟨conditions,hConditions,hProjection⟩ := condition_projection hM hCopies hp.2.2.1
  have hDisj := conditions_disjoint hCopies hTargets hProjection hr hSub hRange hIndependent
  exact ⟨conditions,hConditions,hProjection,fun i hi c hc hRoot =>
    row_hits hM hChoice hw hP hp.1 hp.2.1 hp.2.2.1 hConditions hDisj hA hi hc hRoot⟩

def sourceSentence {k : Nat} (rho : Fin 7 → Fin k)
    (A P I K B w G SF mul bound labels E J delta list targets copies r b p t multipliers : Fin k) : Project.Sentence where
  formula := Project.Formula.forallClosure k
    (.imp (Project.Formula.isOmega (.bound w))
    (.imp (ProjectSyntax.encode id (ForcingProductFamily.presentation (rho 0) I K B w (rho 1) (rho 2) (rho 3) (rho 4) (rho 5) (rho 6)))
    (.imp (ProjectSyntax.encode id (ForcingCohenCoordinates.cartesian A A P))
    (.imp (.neg (ProjectSyntax.encode id (ForcingSupportSize.small A w)))
    (.imp (ForcingOutsideCopies.family (ForcingProductSymmetry.orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G SF) id rho
      G SF w bound labels E J delta list P targets copies)
    (.imp (ForcingOutsideCopies.targets (rho 0) I mul r b p P multipliers targets)
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.injection r (rho 0) I))
    (.imp (ProjectSyntax.encode id (ForcingDiagramOrder.sub (rho 0) mul r t p))
    (.imp (ProjectSyntax.encode id (ForcingSupportedNames.range (rho 0) p J))
    (.imp (independent (rho 0) mul t multipliers)
      (.existsE (.conj (ForcingProbeDensity.copies P.succ 0 (rho 2).succ w.succ J.succ delta.succ)
        (.conj (projection P.succ copies.succ 0)
          (hits A.succ 0 (rho 3).succ delta.succ))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
      ForcingOutsideCopies.family_freeClosed,ForcingOutsideCopies.targets_freeClosed,independent_freeClosed,
      ForcingProbeDensity.copies_freeClosed,projection_freeClosed,hits_freeClosed]

theorem source_models {k : Nat} (rho : Fin 7 → Fin k)
    (A P I K B w G SF mul bound labels E J delta list targets copies r b p t multipliers : Fin k)
    (hM : FirstOrder.Theory.Models M nativeZF) (hChoice : ConstructionDirectedCardinality.Choice (M := M)) :
    (Project.fo_sentence (sourceSentence rho A P I K B w G SF mul bound labels E J delta list targets copies r b p t multipliers)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM),SetTheory.Structure.satisfiesSentence_iff]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro env
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_isOmega_iff,Project.Formula.satisfies_neg_iff,
    Project.Term.eval_bound,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingProductFamily.presentation_semantics (M := M),ForcingCohenCoordinates.cartesian_semantics (M := M),
    ForcingSupportSize.small_semantics (M := M),ForcingOutsideCopies.family_semantics hM,ForcingOutsideCopies.targets_semantics hM,
    ForcingSupportSize.injection_semantics (M := M),ForcingDiagramOrder.sub_semantics (M := M),
    ForcingSupportedNames.range_semantics (M := M),independent_semantics hM]
  intro hw hp hP hA hCopies hTargets hr hSub hRange hIndependent
  simp only [Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    ForcingProbeDensity.copies_semantics hM,projection_semantics hM,hits_semantics hM]
  exact source_construct hM hChoice env rho G SF mul hw hp hP hA hCopies hTargets hr hSub hRange hIndependent

theorem source_kernel_certificate {k : Nat} (rho : Fin 7 → Fin k)
    (A P I K B w G SF mul bound labels E J delta list targets copies r b p t multipliers : Fin k) : FirstOrder.Derives nativeZF []
    (Project.fo_sentence (ConstructibleGround.relative (sourceSentence rho A P I K B w G SF mul bound labels E J delta list targets copies r b p t multipliers))) := by
  apply ModelTransfer.derives
  intro N hN
  have hL := ConstructibleSource.model_zf hN
  have hRawChoice := (Project.FirstOrderSemantics.sentence_correct
    (ModelTransfer.extensionality hL) Axioms.choice).mp (ConstructibleSource.model_choice hN)
  let inhabitant := Classical.choice ((ConstructibleSource.model hN).nonempty .set)
  let env : Env (Project.FirstOrderSemantics.reduct (ConstructibleSource.model hN)) 0 := ⟨Fin.elim0,fun _ => inhabitant⟩
  have hSat : Project.Formula.satisfies env (ConstructionDirectedCardinality.choice (m := 0)) := by
    change Project.Formula.satisfies env (Axioms.choice.formula.rename Fin.elim0)
    rw [Project.Formula.satisfies_rename]
    exact hRawChoice env.free
  have hChoice := (ConstructionDirectedCardinality.choice_semantics hL env).mp hSat
  apply ConstructibleGround.relative_models hN
  exact (Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hL) _).mp (source_models rho A P I K B w G SF mul bound labels E J delta list targets copies r b p t multipliers hL hChoice)


end PPAC.Migration.ForcingProbeRowHits
