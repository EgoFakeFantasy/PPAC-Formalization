/- Pinned ClassFibers.classFiberEmbedding:470-502.
Consume the actual outside-copy records and the SAME eligible System,
quotient projection and exact availability fiber. Consumer: classFiber_dense_lower. -/
import PPAC.Migration.ForcingOutsideCopies
import PPAC.Migration.ForcingClassProfile
import PPAC.Migration.ForcingSystemFibers

namespace PPAC.Migration.ForcingClassFiberEmbedding
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open Source (Formula)
open ForcingProductSymmetry (orderFormula)
open ForcingProductFamily (Presentation)
open ForcingSupportSize (MapsTo Injection Small)
open ForcingDiagramOrder (Sub Product)
open ForcingEligibleFamily (Data)
open ForcingOutsideCopies (Targets Family)
open ForcingPowerName (trueTest)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 3000000
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

/-- The value is the actual root projection of the SAME name in the copy record. -/
def At (copies projection i x : M.Carrier .set) : Prop :=
  ∃ record d name, PureKuratowski.PairMember M i record copies ∧ PureKuratowski.Code M record d name ∧
    PureKuratowski.PairMember M name x projection

def atValue {n : Nat} (copies projection i x : Fin n) : Project.Formula 1 n :=
  .existsE (.existsE (.existsE (.conj
    (ProjectSyntax.encode id (Source.SetLanguage.edge copies.succ.succ.succ i.succ.succ.succ 2))
    (.conj (ProjectSyntax.encode id (PairSyntax.ordered 2 1 0))
      (ProjectSyntax.encode id (Source.SetLanguage.edge projection.succ.succ.succ 0 x.succ.succ.succ))))))

theorem at_freeClosed {n : Nat} (copies projection i x : Fin n) : (atValue copies projection i x).FreeClosed := by
  simp -implicitDefEqProofs [atValue,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed]

theorem at_semantics (hM : FirstOrder.Theory.Models M nativeZF) {n : Nat}
    (env : Env (Project.FirstOrderSemantics.reduct M) n) (copies projection i x : Fin n) :
    Project.Formula.satisfies env (atValue copies projection i x) ↔
      At (env.bound copies) (env.bound projection) (env.bound i) (env.bound x) := by
  simp only [atValue,At,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,KuratowskiZF.source_code]
  rfl

theorem at_unique {indices copies X projection i x y : M.Carrier .set}
    (hc : ForcingConditionGraphs.FunctionOn indices copies) (hp : ForcingConditionGraphs.FunctionOn X projection)
    (hx : At copies projection i x) (hy : At copies projection i y) : x = y := by
  obtain ⟨record,d,name,hi,hr,hx⟩ := hx
  obtain ⟨record',d',name',hi',hr',hy⟩ := hy
  have eq := ForcingConditionGraphs.function_unique hc hi hi'
  subst record'
  obtain ⟨rfl,rfl⟩ := PureKuratowski.code_injective hr hr'
  exact ForcingConditionGraphs.function_unique hp hx hy

/-- Decode one actual copy and align its support with the existing target Data.
No new local-name carrier, quotient, or target object is chosen independently. -/
theorem entry_data (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    {R : Formula (k+2)} {Hdom : Formula (k+1)} {env : Fin k → M.Carrier .set}
    {v : Fin 7 → M.Carrier .set} {I G F mul g q bound labels E w J delta list r b p indices multipliers targets copies
      oi objects i record d sigma : M.Carrier .set}
    (hDiagrams : ForcingDiagramCarrier.Carrier (v 0) I (v 4))
    (hObj : MapsTo (v 4) oi objects)
    (hFamily : ForcingEligibleFamily.Family R Hdom env v G F mul g q bound labels E (v 4) objects)
    (hTargets : Targets (v 0) I mul r b p indices multipliers targets)
    (hCopies : Family R Hdom env v G F w bound labels E J delta list indices targets copies)
    (hi : PureKuratowski.PairMember M i record copies) (hRecord : PureKuratowski.Code M record d sigma) :
    ∃ m sm Om Am Hm XM QM prM z,
      PureKuratowski.PairMember M i m multipliers ∧ Injection (v 0) I sm ∧ Sub (v 0) mul r m sm ∧ Sub (v 0) mul sm b p ∧
      PureKuratowski.PairMember M sm Om objects ∧ Data R Hdom env v G F mul g q bound labels E sm Am Hm XM QM prM Om ∧
      ForcingLocalNames.LocalName v G F bound Hm sigma ∧ ForcingSupportingRoot.Code z d sm ∧
      (∀ a, (Project.FirstOrderSemantics.reduct M).mem a (v 6) →
        ForcingFormula.Force R Hdom env (Source.SetLanguage.args3 sigma labels E) (v 6) a (ForcingEligibility.isClass 0 1 2)) ∧
      ForcingOutsideLocal.Outside R env (v 6) z sigma list := by
  obtain ⟨sm,hsm,d',sigma',A,Hs,z,hRec,_,_,_,hA,hHs,hLocal,hCode,hClass,hOut⟩ := hCopies.2 i record hi
  obtain ⟨rfl,rfl⟩ := PureKuratowski.code_injective hRecord hRec
  obtain ⟨hsmI,hRoot,m,him,hSub⟩ := hTargets.2 i sm hsm
  obtain ⟨Om,hOm,_⟩ := hObj.1.2 sm ((hDiagrams sm).mpr hsmI)
  obtain ⟨Am,Hm,XM,QM,prM,hData⟩ := ((hFamily sm Om).mp hOm).2
  have eA := (ModelTransfer.extensionality hM).eq_of_same_members A Am (fun x => (hA x).trans (hData.1 x).symm)
  subst Am
  have eH := ForcingLabelPermutations.fixing_unique hM hHs hData.2.1
  subst Hm
  exact ⟨m,sm,Om,A,Hs,XM,QM,prM,z,him,hsmI,hSub,hRoot,hOm,hData,hLocal,hCode,hClass,hOut⟩

theorem construct (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (G F mul : Fin k)
    {w mu history kappa one mark H C incoming base I K B c top bit labels bound g q E oi objects S mi maps
      r p Or OP Ap Hp XP QP prP Ar Hr XR QR prR ordinal enum list a e b t U indices multipliers targets copies delta : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hMu : (Project.FirstOrderSemantics.reduct M).IsInfiniteCardinal (KuratowskiZF.interpretation hM) w mu)
    (hI : (Project.FirstOrderSemantics.reduct M).IsHartogsNumber (KuratowskiZF.interpretation hM) I mu)
    (hD : Small (env (rho 0)) mu) (hMergers : ConstructionSaturationMergers.AllMergers w history kappa)
    (hRow : ConstructionTowerHistory.Row history kappa (env (rho 0)) (env mul) one mark H C incoming base kappa)
    (hm : ForcingDiagramPoset.LeftCancelMonoid (env (rho 0)) (env mul) one)
    (hp : Presentation (env (rho 0)) I K B w (env (rho 1)) (env (rho 2)) (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hG : ForcingLabelPermutations.Carrier I (env G)) (hF : ForcingSupportFilter.Filter I (env G) mu (env F))
    (hc : ForcingConditionGraphs.FunctionOn K c) (ht : ForcingWithTopCarrier.Empty top)
    (hLabels : ForcingLabelSet.LabelSet (env (rho 6)) I K c top bit labels)
    (hBound : ForcingLabelBound.LabelBound (env (rho 6)) I K c top bit bound)
    (hg : ForcingLocalAtomic.CohenFilter (env (rho 3)) g)
    (hObj : MapsTo (env (rho 4)) oi objects)
    (hObjFamily : ForcingEligibleFamily.Family (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) env
      (fun j => env (rho j)) (env G) (env F) (env mul) g q bound labels E (env (rho 4)) objects)
    (hArrows : ForcingEligibleMapFamily.Arrows (env (rho 0)) (env mul) (env (rho 4)) S)
    (hMaps : MapsTo S mi maps)
    (hMapFamily : ForcingEligibleMapFamily.Family (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) env
      (fun j => env (rho j)) (env G) (env F) (env mul) g q bound labels E S maps)
    (hSys : ForcingEligibleSystem.System (env (rho 0)) objects maps)
    (hr : PureKuratowski.PairMember M r Or objects) (hP : PureKuratowski.PairMember M p OP objects)
    (hDP : Data (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) env (fun j => env (rho j))
      (env G) (env F) (env mul) g q bound labels E p Ap Hp XP QP prP OP)
    (hDR : Data (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) env (fun j => env (rho j))
      (env G) (env F) (env mul) g q bound labels E r Ar Hr XR QR prR Or)
    (hq : Injection (env (rho 0)) I q)
    (ha : (Project.FirstOrderSemantics.reduct M).mem a (env (rho 0)))
    (he : (Project.FirstOrderSemantics.reduct M).mem e (env (rho 0)))
    (hb : (Project.FirstOrderSemantics.reduct M).mem b (env (rho 0)))
    (hae : Product (env mul) a e t)
    (hSuba : Sub (env (rho 0)) (env mul) r a q)
    (hSubp : Sub (env (rho 0)) (env mul) r t p)
    (hEnum : (Project.FirstOrderSemantics.reduct M).IsSetBijectionFromTo (KuratowskiZF.interpretation hM) enum ordinal XP)
    (hList : ForcingCollectedName.Collected trueTest Fin.elim0 ordinal enum (env (rho 6)) list)
    (hMuls : MapsTo indices (env (rho 0)) multipliers)
    (hProducts : ∀ i m, PureKuratowski.PairMember M i m multipliers → Product (env mul) m b t)
    (hTargets : Targets (env (rho 0)) I (env mul) r b p indices multipliers targets)
    (hCopies : Family (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) env (fun j => env (rho j))
      (env G) (env F) w bound labels E Ap delta list indices targets copies)
    (hHits : ∀ i record d sigma, PureKuratowski.PairMember M i record copies → PureKuratowski.Code M record d sigma →
      (Project.FirstOrderSemantics.reduct M).mem d g)
    (hGeometry : ∀ i m, PureKuratowski.PairMember M i m multipliers →
      ForcingClassProfile.Geometry (env (rho 0)) (env mul) a m t U)
    (hIndependent : ∀ i j m n, PureKuratowski.PairMember M i m multipliers → PureKuratowski.PairMember M j n multipliers →
      i ≠ j → ConstructionDiagramPlacements.ConeEquality (env (rho 0)) (env mul) m n t) :
    ∃ V embedding, ForcingSystemFibers.Fiber (env (rho 0)) (env mul) objects maps r Or a U V ∧
      Injection indices V embedding ∧ ∀ i x, PureKuratowski.PairMember M i x embedding ↔
        (Project.FirstOrderSemantics.reduct M).mem i indices ∧ At copies prR i x := by
  have hrI := (hp.2.2.2.1 r).mp (ForcingConditionGraphs.function_input hObj.1 hr)
  have hpI := (hp.2.2.2.1 p).mp (ForcingConditionGraphs.function_input hObj.1 hP)
  obtain ⟨V,hV⟩ := ForcingSystemFibers.exists_fiber hM (env (rho 0)) (env mul) objects maps r Or a U
  have one_value : ∀ i, (Project.FirstOrderSemantics.reduct M).mem i indices →
      ∃ x, (Project.FirstOrderSemantics.reduct M).mem x V ∧ At copies prR i x := by
    intro i hi
    obtain ⟨record,hir,_⟩ := hCopies.1.2 i hi
    obtain ⟨_,_,d,sigma,_,_,_,hRec,_⟩ := hCopies.2 i record hir
    obtain ⟨m,sm,Om,Am,Hm,XM,QM,prM,z,him,hsmI,hSubm,_,hsm,hDM,hLocal,hCode,hClass,hOut⟩ :=
      entry_data hM hp.2.2.2.1 hObj hObjFamily hTargets hCopies hir hRec
    have hd := hHits i record d sigma hir hRec
    have hel : ForcingEligibility.EligibleName (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F)
        env (env (rho 6)) g sm labels E sigma :=
      ⟨d,z,hd,hCode,hClass z (ForcingSupportingRoot.code_mem hp ((hp.2.2.1 d).mp (hg.1 d hd)) hsmI hCode)⟩
    obtain ⟨x,hx,hpr,hProfile⟩ := ForcingClassProfile.construct hM hChoice env rho G F mul hw hMu hI hD hMergers hRow hm hp hG hF hc ht hLabels hBound hg
      hObj hObjFamily hArrows hMaps hMapFamily hSys hr hP hsm hDP hDM hDR hq ha he (hMuls.2 i m him) hb hae (hProducts i m him)
      hSuba hSubm hSubp hLocal hel hEnum hList hd hCode hOut (hGeometry i m him)
    exact ⟨x,(hV x).mpr ⟨hx,hProfile⟩,record,d,sigma,hir,hRec,hpr⟩
  let schema : Project.BinarySchema 2 := {
    body := atValue (0 : Fin 2).succ.succ (1 : Fin 2).succ.succ 1 0
    freeClosed := at_freeClosed _ _ _ _ }
  let penv : Env (Project.FirstOrderSemantics.reduct M) 2 := ⟨Source.SetLanguage.args2 copies prR,fun _ => Or⟩
  have hRel i x : schema.denote penv i x ↔ At copies prR i x := by
    simp only [schema,Project.BinarySchema.denote,at_semantics hM]
    rfl
  obtain ⟨embedding,hEmbedding,hEdge⟩ := ZF.exists_setFunctionFromTo_of_denote
    (ModelTransfer.project_models_iff.mp hM) (KuratowskiZF.interpretation hM) schema penv (source := indices) (target := V)
    (fun i hi => by obtain ⟨x,_,hx⟩ := one_value i hi; exact ⟨x,(hRel i x).mpr hx⟩)
    (fun i _ x y hx hy => at_unique hCopies.1 hDR.2.2.2.1.1 ((hRel i x).mp hx) ((hRel i y).mp hy)) (by
      intro i x hi hx
      obtain ⟨y,hy,hiy⟩ := one_value i hi
      have eq := at_unique hCopies.1 hDR.2.2.2.1.1 ((hRel i x).mp hx) hiy
      exact eq.symm ▸ hy)
  have hExact : ∀ i x, PureKuratowski.PairMember M i x embedding ↔
      (Project.FirstOrderSemantics.reduct M).mem i indices ∧ At copies prR i x :=
    fun i x => (hEdge i x).trans (and_congr Iff.rfl (hRel i x))
  refine ⟨V,embedding,hV,⟨(ForcingSupportSize.native_mapsTo hM _ _ _).mpr hEmbedding,?_⟩,hExact⟩
  intro i j x hix hjx
  apply Classical.byContradiction
  intro hij
  obtain ⟨record0,d0,sigma0,hi0,hRec0,hProj0⟩ := ((hExact i x).mp hix).2
  obtain ⟨record1,d1,sigma1,hj1,hRec1,hProj1⟩ := ((hExact j x).mp hjx).2
  obtain ⟨m,sm,Om,Am,Hm,XM,QM,prM,z0,him,hsmI,hSubm,hRootM,_,hDM,hLocal0,hCode0,_,hOut0⟩ :=
    entry_data hM hp.2.2.2.1 hObj hObjFamily hTargets hCopies hi0 hRec0
  obtain ⟨n,sn,On,An,Hn,XN,QN,prN,z1,hjn,hsnI,hSubn,hRootN,_,hDN,hLocal1,_,_,_⟩ :=
    entry_data hM hp.2.2.2.1 hObj hObjFamily hTargets hCopies hj1 hRec1
  have hInter := ConstructionDiagramPlacements.range_inter_sub hrI hSubm hSubn hSubp (hIndependent i j m n him hjn hij)
  have hEq := (ForcingLocalQuotient.equality_law hM env rho mul hm hp hg hrI hDR.2.2.2.2.2.1
    sigma0 sigma1 x x hProj0 hProj1).mp rfl
  exact ForcingClassProfile.outside_not_eqG_common hM hChoice env rho G F mul hw hMu hI hD hMergers hRow hm hp hG hF
    hpI hsmI hsnI hrI ⟨b,hb,hRootM⟩ ⟨b,hb,hRootN⟩ hInter ⟨m,hMuls.2 i m him,hSubm⟩ ⟨n,hMuls.2 j n hjn,hSubn⟩
    hDM.1 hDN.1 hDP.1 hDM.2.1 hDN.2.1 hDP.2.1 hLocal0 hLocal1 hc ht hLabels hBound hg hDP.2.2.1 hEnum hList
    (hHits i record0 d0 sigma0 hi0 hRec0) hCode0 hOut0 hEq


/-- The source's common product, actual filter hits, profiles and independent probes.
All indices and records are object variables, including nonstandard internal indices. -/
def inputConditions {k : Nat} (D mul a b t U g multipliers copies : Fin k) : Project.Formula 1 k :=
  .conj (.forallE (.forallE (.imp
    (ProjectSyntax.encode id (Source.SetLanguage.edge multipliers.succ.succ 1 0))
    (ProjectSyntax.encode id (ForcingDiagramOrder.product mul.succ.succ 0 b.succ.succ t.succ.succ)))))
  (.conj (.forallE (.forallE (.forallE (.forallE (.imp
    (ProjectSyntax.encode id (Source.SetLanguage.edge copies.succ.succ.succ.succ 3 2))
    (.imp (ProjectSyntax.encode id (PairSyntax.ordered 2 1 0))
      (.mem (.bound 1) (.bound g.succ.succ.succ.succ))))))))
  (.conj (.forallE (.forallE (.imp
    (ProjectSyntax.encode id (Source.SetLanguage.edge multipliers.succ.succ 1 0))
    (ForcingClassProfile.geometry D.succ.succ mul.succ.succ a.succ.succ 0 t.succ.succ U.succ.succ))))
    (.forallE (.forallE (.forallE (.forallE (.imp
      (ProjectSyntax.encode id (Source.SetLanguage.edge multipliers.succ.succ.succ.succ 3 1))
      (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge multipliers.succ.succ.succ.succ 2 0))
        (.imp (.neg (Project.Formula.extensionalEq (.bound 3) (.bound 2)))
          (ConstructionDiagramPlacements.coneEquality D.succ.succ.succ.succ mul.succ.succ.succ.succ 1 0 t.succ.succ.succ.succ))))))))))

theorem inputConditions_freeClosed {k : Nat} (D mul a b t U g multipliers copies : Fin k) :
    (inputConditions D mul a b t U g multipliers copies).FreeClosed := by
  simp -implicitDefEqProofs [inputConditions,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
    ForcingClassProfile.geometry_freeClosed,ConstructionDiagramPlacements.coneEquality_freeClosed]

theorem inputConditions_semantics (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Env (Project.FirstOrderSemantics.reduct M) k) (D mul a b t U g multipliers copies : Fin k) :
    Project.Formula.satisfies env (inputConditions D mul a b t U g multipliers copies) ↔
      (∀ i m, PureKuratowski.PairMember M i m (env.bound multipliers) → Product (env.bound mul) m (env.bound b) (env.bound t)) ∧
      (∀ i record d sigma, PureKuratowski.PairMember M i record (env.bound copies) → PureKuratowski.Code M record d sigma →
        (Project.FirstOrderSemantics.reduct M).mem d (env.bound g)) ∧
      (∀ i m, PureKuratowski.PairMember M i m (env.bound multipliers) →
        ForcingClassProfile.Geometry (env.bound D) (env.bound mul) (env.bound a) m (env.bound t) (env.bound U)) ∧
      (∀ i j m n, PureKuratowski.PairMember M i m (env.bound multipliers) → PureKuratowski.PairMember M j n (env.bound multipliers) →
        i ≠ j → ConstructionDiagramPlacements.ConeEquality (env.bound D) (env.bound mul) m n (env.bound t)) := by
  simp only [inputConditions,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_neg_iff,Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM),
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,KuratowskiZF.source_code,
    ForcingDiagramOrder.product_semantics (M := M),ForcingClassProfile.geometry_semantics hM,
    ConstructionDiagramPlacements.coneEquality_semantics hM]
  rfl

/-- Existentially bind the actual fiber and its exact injection graph. -/
def result {k : Nat} (D mul objects maps r Or a U indices copies prR : Fin k) : Project.Formula 1 k :=
  let edge : Project.Formula 1 (k+2+2) := ProjectSyntax.encode id (Source.SetLanguage.edge 2 1 0)
  let value : Project.Formula 1 (k+2+2) := .conj (.mem (.bound 1) (.bound indices.succ.succ.succ.succ))
    (atValue copies.succ.succ.succ.succ prR.succ.succ.succ.succ 1 0)
  .existsE (.existsE (.conj
    (ProjectSyntax.encode id (ForcingSystemFibers.fiber D.succ.succ mul.succ.succ objects.succ.succ maps.succ.succ
      r.succ.succ Or.succ.succ a.succ.succ U.succ.succ 1))
    (.conj (ProjectSyntax.encode id (Source.SetLanguage.injection 0 indices.succ.succ 1))
      (.forallE (.forallE (.conj (.imp edge value) (.imp value edge)))))))

theorem result_semantics (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Env (Project.FirstOrderSemantics.reduct M) k) (D mul objects maps r Or a U indices copies prR : Fin k) :
    Project.Formula.satisfies env (result D mul objects maps r Or a U indices copies prR) ↔
      ∃ V embedding, ForcingSystemFibers.Fiber (env.bound D) (env.bound mul) (env.bound objects) (env.bound maps)
        (env.bound r) (env.bound Or) (env.bound a) (env.bound U) V ∧ Injection (env.bound indices) V embedding ∧
        ∀ i x, PureKuratowski.PairMember M i x embedding ↔
          (Project.FirstOrderSemantics.reduct M).mem i (env.bound indices) ∧ At (env.bound copies) (env.bound prR) i x := by
  simp only [result,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_mem_iff,
    Project.Term.eval_bound,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingSystemFibers.fiber_semantics (M := M),ForcingSupportSize.injection_semantics (M := M),
    KuratowskiZF.source_edge,at_semantics hM]
  constructor
  · rintro ⟨V,f,hV,hf,he⟩
    exact ⟨V,f,hV,hf,fun i x => ⟨(he i x).1,(he i x).2⟩⟩
  · rintro ⟨V,f,hV,hf,he⟩
    exact ⟨V,f,hV,hf,fun i x => ⟨(he i x).mp,(he i x).mpr⟩⟩

def constructionSentence {k : Nat} (rho : Fin 7 → Fin k)
    (w mu history kappa one mark H C incoming base I K B G F mul c top bit labels bound g q E oi objects S mi maps r p Or OP Ap Hp XP QP prP Ar Hr XR QR prR ordinal enum list a e b t U indices multipliers targets copies delta : Fin k) : Project.Sentence where
  formula := Project.Formula.forallClosure k
    (.imp (Project.Formula.isOmega (.bound w))
    (.imp (Project.Formula.isInfiniteCardinal PureKuratowskiProject.convention (.bound w) (.bound mu))
    (.imp (ConstructionSaturationIndex.hartogs mu I)
    (.imp (ProjectSyntax.encode id (ForcingSupportSize.small (rho 0) mu))
    (.imp (ConstructionSaturationMergers.allMergers w history kappa)
    (.imp (ConstructionTowerHistory.row history kappa (rho 0) mul one mark H C incoming base kappa)
    (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid (rho 0) mul one))
    (.imp (ProjectSyntax.encode id (ForcingProductFamily.presentation (rho 0) I K B w (rho 1) (rho 2) (rho 3) (rho 4) (rho 5) (rho 6)))
    (.imp (ProjectSyntax.encode id (ForcingLabelPermutations.carrier I G))
    (.imp (ProjectSyntax.encode id (ForcingSupportFilter.filter I G mu F))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.functionOn c K))
    (.imp (ProjectSyntax.encode id (ForcingWithTopCarrier.empty top))
    (.imp (ProjectSyntax.encode id (ForcingLabelSet.labelSet (rho 6) I K c top bit labels))
    (.imp (ProjectSyntax.encode id (ForcingLabelBound.labelBound (rho 6) I K c top bit bound))
    (.imp (ProjectSyntax.encode id (ForcingLocalAtomic.cohenFilter (rho 3) g))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.mapsTo objects (rho 4) oi))
    (.imp (ProjectSyntax.encode id (ForcingEligibleFamily.family (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) id rho G F mul g q bound labels E (rho 4) objects))
    (.imp (ProjectSyntax.encode id (ForcingEligibleMapFamily.arrows (rho 0) mul (rho 4) S))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.mapsTo maps S mi))
    (.imp (ProjectSyntax.encode id (ForcingEligibleMapFamily.family (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) id rho G F mul g q bound labels E S maps))
    (.imp (ForcingEligibleSystem.system (rho 0) objects maps)
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge objects r Or))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge objects p OP))
    (.imp (ProjectSyntax.encode id (ForcingEligibleFamily.data (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) id rho G F mul g q bound labels E p Ap Hp XP QP prP OP))
    (.imp (ProjectSyntax.encode id (ForcingEligibleFamily.data (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) id rho G F mul g q bound labels E r Ar Hr XR QR prR Or))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.injection q (rho 0) I))
    (.imp (.mem (.bound a) (.bound (rho 0)))
    (.imp (.mem (.bound e) (.bound (rho 0)))
    (.imp (.mem (.bound b) (.bound (rho 0)))
    (.imp (ProjectSyntax.encode id (ForcingDiagramOrder.product mul a e t))
    (.imp (ProjectSyntax.encode id (ForcingDiagramOrder.sub (rho 0) mul r a q))
    (.imp (ProjectSyntax.encode id (ForcingDiagramOrder.sub (rho 0) mul r t p))
    (.imp (Project.Formula.isBijectionFromTo PureKuratowskiProject.convention (.bound enum) (.bound ordinal) (.bound XP))
    (.imp (ProjectSyntax.encode id (ForcingCollectedName.collected trueTest Fin.elim0 ordinal enum (rho 6) list))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.mapsTo multipliers indices (rho 0)))
    (.imp (ForcingOutsideCopies.targets (rho 0) I mul r b p indices multipliers targets)
    (.imp (ForcingOutsideCopies.family (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) id rho G F w bound labels E Ap delta list indices targets copies)
    (.imp (inputConditions (rho 0) mul a b t U g multipliers copies)
      (result (rho 0) mul objects maps r Or a U indices copies prR)))))))))))))))))))))))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [result,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
      ConstructionSaturationIndex.hartogs_freeClosed,ConstructionSaturationMergers.allMergers_freeClosed,
      ConstructionTowerHistory.row_freeClosed,ForcingEligibleSystem.system_freeClosed,ForcingOutsideCopies.targets_freeClosed,
      ForcingOutsideCopies.family_freeClosed,inputConditions_freeClosed,at_freeClosed]

theorem construction_models {k : Nat} (rho : Fin 7 → Fin k)
    (w mu history kappa one mark H C incoming base I K B G F mul c top bit labels bound g q E oi objects S mi maps r p Or OP Ap Hp XP QP prP Ar Hr XR QR prR ordinal enum list a e b t U indices multipliers targets copies delta : Fin k)
    (hM : FirstOrder.Theory.Models M nativeZF) (hChoice : ConstructionDirectedCardinality.Choice (M := M)) :
    (Project.fo_sentence (constructionSentence rho w mu history kappa one mark H C incoming base I K B G F mul c top bit labels bound g q E oi objects S mi maps r p Or OP Ap Hp XP QP prP Ar Hr XR QR prR ordinal enum list a e b t U indices multipliers targets copies delta)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM),SetTheory.Structure.satisfiesSentence_iff]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro env
  simp only [Project.Formula.satisfies_imp_iff,Project.Term.eval_bound,Project.Formula.satisfies_mem_iff,
    Project.Formula.satisfies_isOmega_iff,
    Project.Formula.satisfies_isInfiniteCardinal_iff (KuratowskiZF.interpretation hM) (ModelTransfer.extensionality hM),
    ConstructionSaturationIndex.hartogs_semantics hM,ConstructionSaturationMergers.allMergers_semantics hM,ConstructionTowerHistory.row_semantics hM,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ForcingSupportSize.small_semantics (M := M),
    ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),ForcingProductFamily.presentation_semantics (M := M),
    ForcingLabelPermutations.carrier_semantics (M := M),ForcingSupportFilter.filter_semantics (M := M),
    ForcingConditionGraphs.functionOn_semantics (M := M),ForcingWithTopCarrier.empty_semantics (M := M),
    ForcingLabelSet.labelSet_semantics (M := M),ForcingLabelBound.labelBound_semantics (M := M),
    ForcingLocalAtomic.cohenFilter_semantics (M := M),ForcingSupportSize.mapsTo_semantics (M := M),
    ForcingEligibleFamily.family_semantics (M := M),ForcingEligibleMapFamily.arrows_semantics (M := M),ForcingEligibleMapFamily.family_semantics (M := M),
    ForcingEligibleSystem.system_semantics hM,KuratowskiZF.source_edge,ForcingEligibleFamily.data_semantics (M := M),
    ForcingSupportSize.injection_semantics (M := M),ForcingDiagramOrder.product_semantics (M := M),ForcingDiagramOrder.sub_semantics (M := M),
    
    Project.Formula.satisfies_isBijectionFromTo_iff (KuratowskiZF.interpretation hM) (ModelTransfer.extensionality hM),
    ForcingCollectedName.collected_semantics (M := M),
    ForcingOutsideCopies.targets_semantics hM,ForcingOutsideCopies.family_semantics hM,inputConditions_semantics hM]
  intro hw hMu hI hD hMergers hRow hm hp hG hF hc ht hLabels hBound hg hObj hObjFamily hArrows hMaps hMapFamily hSys hr hP hDP hDR hq ha he hb hae hSuba hSubp hEnum hList hMuls hTargets hCopies hInputs
  obtain ⟨hProducts,hHits,hGeometry,hIndependent⟩ := hInputs
  apply (result_semantics hM _ _ _ _ _ _ _ _ _ _ _ _).mpr
  exact construct hM hChoice env rho G F mul hw hMu hI hD hMergers hRow hm hp hG hF hc ht hLabels hBound hg hObj hObjFamily hArrows hMaps hMapFamily hSys hr hP hDP hDR hq ha he hb hae hSuba hSubp hEnum hList hMuls hProducts hTargets hCopies hHits hGeometry hIndependent

theorem construction_kernel_certificate {k : Nat} (rho : Fin 7 → Fin k)
    (w mu history kappa one mark H C incoming base I K B G F mul c top bit labels bound g q E oi objects S mi maps r p Or OP Ap Hp XP QP prP Ar Hr XR QR prR ordinal enum list a e b t U indices multipliers targets copies delta : Fin k) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (ConstructibleGround.relative
      (constructionSentence rho w mu history kappa one mark H C incoming base I K B G F mul c top bit labels bound g q E oi objects S mi maps r p Or OP Ap Hp XP QP prP Ar Hr XR QR prR ordinal enum list a e b t U indices multipliers targets copies delta))) := by
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
  exact (Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hL) _).mp
    (construction_models rho w mu history kappa one mark H C incoming base I K B G F mul c top bit labels bound g q E oi objects S mi maps r p Or OP Ap Hp XP QP prP Ar Hr XR QR prR ordinal enum list a e b t U indices multipliers targets copies delta hL hChoice)


end PPAC.Migration.ForcingClassFiberEmbedding
