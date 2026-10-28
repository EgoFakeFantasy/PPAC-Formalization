/- Pinned AvailableRecords.eligibleSystem:265-289 and LocalRecords.System:531-544.
Bind every law to the SAME actual internal object and map families. All local
quotient/eligibility mathematics is reused; Data uniqueness aligns witnesses.
The certificate uses the existing internal L, without object Choice in nativeZF. -/
import PPAC.Migration.ForcingEligibleMapFamily

namespace PPAC.Migration.ForcingEligibleSystem
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open Source (Formula)
open ForcingSupportSize (MapsTo Injection Small)
open ForcingEligibleFamily (Data)
open ForcingProductSymmetry (orderFormula)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

theorem map_data (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    {R : Formula (k+2)} {Hdom : Formula (k+1)} {env : Fin k → M.Carrier .set}
    {v : Fin 7 → M.Carrier .set} {G F mul g q nameBound labels E diagrams objects S maps r s Or Os z a : M.Carrier .set}
    (hObj : ForcingEligibleFamily.Family R Hdom env v G F mul g q nameBound labels E diagrams objects)
    (hMaps : ForcingEligibleMapFamily.Family R Hdom env v G F mul g q nameBound labels E S maps)
    (hr : PureKuratowski.PairMember M r Or objects) (hs : PureKuratowski.PairMember M s Os objects)
    (hz : PureKuratowski.Code M z r s) (ha : PureKuratowski.PairMember M z a maps) :
    ∃ Ar Hr Xr Qr pr As Hs Xs Qs ps f,
      Data R Hdom env v G F mul g q nameBound labels E r Ar Hr Xr Qr pr Or ∧
      Data R Hdom env v G F mul g q nameBound labels E s As Hs Xs Qs ps Os ∧
      MapsTo Qr Qs f ∧ ForcingLocalRestriction.Restriction pr ps f ∧
      MapsTo Or Os a ∧ ForcingEligibleRestriction.Restricts a f Or := by
  obtain ⟨r',s',Ar,Hr,Xr,Qr,pr,Or',As,Hs,Xs,Qs,ps,Os',f,hz',hDr,hDs,hf,hR,hMap,hA⟩ := ((hMaps z a).mp ha).2
  obtain ⟨rfl,rfl⟩ := PureKuratowski.code_injective hz hz'
  have her := ForcingEligibleFamily.row_unique hM ((hObj r Or).mp hr).2 ⟨Ar,Hr,Xr,Qr,pr,hDr⟩
  have hes := ForcingEligibleFamily.row_unique hM ((hObj s Os).mp hs).2 ⟨As,Hs,Xs,Qs,ps,hDs⟩
  subst Or'; subst Os'
  exact ⟨Ar,Hr,Xr,Qr,pr,As,Hs,Xs,Qs,ps,f,hDr,hDs,hf,hR,hMap,hA⟩

theorem map_order {k : Nat}
    {R : Formula (k+2)} {Hdom : Formula (k+1)} {env : Fin k → M.Carrier .set}
    {v : Fin 7 → M.Carrier .set} {G F mul g q nameBound labels E diagrams S maps r s z a : M.Carrier .set}
    (hS : ForcingEligibleMapFamily.Arrows (v 0) mul diagrams S)
    (hMaps : ForcingEligibleMapFamily.Family R Hdom env v G F mul g q nameBound labels E S maps)
    (hz : PureKuratowski.Code M z r s) (ha : PureKuratowski.PairMember M z a maps) :
    ForcingDiagramOrder.Le (v 0) mul s r := by
  obtain ⟨r',s',_,_,hle,hz'⟩ := (hS z).mp ((hMaps z a).mp ha).1
  obtain ⟨rfl,rfl⟩ := PureKuratowski.code_injective hz hz'
  exact hle

def Identity (objects maps : M.Carrier .set) : Prop :=
  ∀ r Or z a, PureKuratowski.PairMember M r Or objects → PureKuratowski.Code M z r r →
    PureKuratowski.PairMember M z a maps → ForcingConditionGraphs.IdentityGraph Or a

def Composition (objects maps : M.Carrier .set) : Prop :=
  ∀ r s t Or Os Ot z01 z12 z02 a01 a12 a02,
    PureKuratowski.PairMember M r Or objects → PureKuratowski.PairMember M s Os objects →
    PureKuratowski.PairMember M t Ot objects →
    PureKuratowski.Code M z01 r s → PureKuratowski.Code M z12 s t → PureKuratowski.Code M z02 r t →
    PureKuratowski.PairMember M z01 a01 maps → PureKuratowski.PairMember M z12 a12 maps →
    PureKuratowski.PairMember M z02 a02 maps → ForcingConditionGraphs.CompositionGraph Or a12 a01 a02

def Injective (objects maps : M.Carrier .set) : Prop :=
  ∀ r s Or Os z a, PureKuratowski.PairMember M r Or objects → PureKuratowski.PairMember M s Os objects →
    PureKuratowski.Code M z r s → PureKuratowski.PairMember M z a maps → Injection Or Os a

def Intersection (D objects maps : M.Carrier .set) : Prop :=
  ∀ p s0 s1 v OP O0 O1 OV z0 z1 zk0 zk1 a0 a1 b0 b1 x0 x1 y,
    PureKuratowski.PairMember M p OP objects → PureKuratowski.PairMember M s0 O0 objects →
    PureKuratowski.PairMember M s1 O1 objects → PureKuratowski.PairMember M v OV objects →
    PureKuratowski.Code M z0 s0 v → PureKuratowski.Code M z1 s1 v →
    PureKuratowski.Code M zk0 p s0 → PureKuratowski.Code M zk1 p s1 →
    PureKuratowski.PairMember M z0 a0 maps → PureKuratowski.PairMember M z1 a1 maps →
    PureKuratowski.PairMember M zk0 b0 maps → PureKuratowski.PairMember M zk1 b1 maps →
    ConstructionDiagramPlacements.RangeIntersection D s0 s1 p →
    PureKuratowski.PairMember M x0 y a0 → PureKuratowski.PairMember M x1 y a1 →
    ∃ x, (Project.FirstOrderSemantics.reduct M).mem x OP ∧
      PureKuratowski.PairMember M x x0 b0 ∧ PureKuratowski.PairMember M x x1 b1

def System (D objects maps : M.Carrier .set) : Prop :=
  ForcingEligibleMapFamily.Compatible objects maps ∧ Identity objects maps ∧
    Composition objects maps ∧ Injective objects maps ∧ Intersection D objects maps

theorem identity_of_families (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    {R : Formula (k+2)} {Hdom : Formula (k+1)} {env : Fin k → M.Carrier .set}
    {v : Fin 7 → M.Carrier .set} {G F mul g q nameBound labels E diagrams objects S maps : M.Carrier .set}
    (hObj : ForcingEligibleFamily.Family R Hdom env v G F mul g q nameBound labels E diagrams objects)
    (hMaps : ForcingEligibleMapFamily.Family R Hdom env v G F mul g q nameBound labels E S maps) : Identity objects maps := by
  intro r Or z a hr hz ha
  obtain ⟨Ar,Hr,Xr,Qr,pr,As,Hs,Xs,Qs,ps,f,hDr,hDs,_,hR,_,hA⟩ := map_data hM hObj hMaps hr hr hz ha
  obtain ⟨rfl,rfl,rfl,rfl,rfl,_⟩ := ForcingEligibleFamily.data_unique hM hDr hDs
  obtain ⟨_,_,_,hpr,hQr,hPr,hOr⟩ := hDr
  exact ForcingEligibleRestriction.restrict_refl
    (ForcingLocalRestriction.restrict_refl hpr hQr hPr hR) (fun x hx => ((hOr x).mp hx).1) hA

theorem composition_of_families (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    {R : Formula (k+2)} {Hdom : Formula (k+1)} {env : Fin k → M.Carrier .set}
    {v : Fin 7 → M.Carrier .set} {G F mul g q nameBound labels E diagrams objects S maps : M.Carrier .set}
    (hObj : ForcingEligibleFamily.Family R Hdom env v G F mul g q nameBound labels E diagrams objects)
    (hS : ForcingEligibleMapFamily.Arrows (v 0) mul diagrams S)
    (hMaps : ForcingEligibleMapFamily.Family R Hdom env v G F mul g q nameBound labels E S maps) : Composition objects maps := by
  intro r s t Or Os Ot z01 z12 z02 a01 a12 a02 hr hs ht hz01 hz12 hz02 ha01 ha12 ha02
  have hsr := map_order hS hMaps hz01 ha01
  have hts := map_order hS hMaps hz12 ha12
  obtain ⟨Ar,Hr,Xr,Qr,pr,As,Hs,Xs,Qs,ps,f01,hDr,hDs,_,h01,ha,hA01⟩ := map_data hM hObj hMaps hr hs hz01 ha01
  obtain ⟨As',Hs',Xs',Qs',ps',At,Ht,Xt,Qt,pt,f12,hDs',hDt,hf12,h12,_,hA12⟩ := map_data hM hObj hMaps hs ht hz12 ha12
  obtain ⟨Ar',Hr',Xr',Qr',pr',At',Ht',Xt',Qt',pt',f02,hDr',hDt',_,h02,_,hA02⟩ := map_data hM hObj hMaps hr ht hz02 ha02
  obtain ⟨rfl,rfl,rfl,rfl,rfl,_⟩ := ForcingEligibleFamily.data_unique hM hDs hDs'
  obtain ⟨rfl,rfl,rfl,rfl,rfl,_⟩ := ForcingEligibleFamily.data_unique hM hDr hDr'
  obtain ⟨rfl,rfl,rfl,rfl,rfl,_⟩ := ForcingEligibleFamily.data_unique hM hDt hDt'
  obtain ⟨hAr,hHr,hXr,hpr,_,_,hOr⟩ := hDr
  obtain ⟨hAs,hHs,hXs,hps,_,_,_⟩ := hDs
  obtain ⟨hAt,hHt,hXt,hpt,_,_,_⟩ := hDt
  have hRS : ForcingPowerName.Subset Ar As := fun z hz =>
    (hAs z).mpr (ConstructionDescentPlacement.range_antitone hsr ((hAr z).mp hz))
  have hST : ForcingPowerName.Subset As At := fun z hz =>
    (hAt z).mpr (ConstructionDescentPlacement.range_antitone hts ((hAs z).mp hz))
  have hXY := ForcingLocalNames.restrict_name hHr hHs hRS hXr hXs
  have hYZ := ForcingLocalNames.restrict_name hHs hHt hST hXs hXt
  exact ForcingEligibleRestriction.restrict_comp
    (ForcingLocalRestriction.restrict_restrict hXY hYZ hpr hps hpt hf12 h01 h12 h02)
    (fun x hx => ((hOr x).mp hx).1) hA01 hA12 hA02 ha

theorem system_of_families (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (G F mul : Fin k)
    {w mu history kappa e mark H C incoming base I K B c t b labels nameBound g q Aq fixingQ E objects S maps : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hMu : (Project.FirstOrderSemantics.reduct M).IsInfiniteCardinal (KuratowskiZF.interpretation hM) w mu)
    (hI : (Project.FirstOrderSemantics.reduct M).IsHartogsNumber (KuratowskiZF.interpretation hM) I mu)
    (hD : Small (env (rho 0)) mu) (hMergers : ConstructionSaturationMergers.AllMergers w history kappa)
    (hRow : ConstructionTowerHistory.Row history kappa (env (rho 0)) (env mul) e mark H C incoming base kappa)
    (hm : ForcingDiagramPoset.LeftCancelMonoid (env (rho 0)) (env mul) e)
    (hpres : ForcingProductFamily.Presentation (env (rho 0)) I K B w (env (rho 1)) (env (rho 2))
      (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hG : ForcingLabelPermutations.Carrier I (env G)) (hFilter : ForcingSupportFilter.Filter I (env G) mu (env F))
    (hc : ForcingConditionGraphs.FunctionOn K c) (ht : ForcingWithTopCarrier.Empty t)
    (hLabels : ForcingLabelSet.LabelSet (env (rho 6)) I K c t b labels)
    (hBound : ForcingLabelBound.LabelBound (env (rho 6)) I K c t b nameBound)
    (hg : ForcingLocalAtomic.CohenFilter (env (rho 3)) g)
    (hq : Injection (env (rho 0)) I q)
    (hRangeQ : ForcingSupportedNames.Range (env (rho 0)) q Aq)
    (hFixQ : ForcingLabelPermutations.Fixing (env G) Aq fixingQ)
    (hE : ForcingSupportedNames.Supported (fun i => env (rho i)) fixingQ E)
    (hObj : ForcingEligibleFamily.Family (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) env
      (fun i => env (rho i)) (env G) (env F) (env mul) g q nameBound labels E (env (rho 4)) objects)
    (hS : ForcingEligibleMapFamily.Arrows (env (rho 0)) (env mul) (env (rho 4)) S)
    (hMaps : ForcingEligibleMapFamily.Family (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) env
      (fun i => env (rho i)) (env G) (env F) (env mul) g q nameBound labels E S maps) :
    System (env (rho 0)) objects maps := by
  refine ⟨ForcingEligibleMapFamily.compatible_of_families hM hObj hMaps,
    identity_of_families hM hObj hMaps,composition_of_families hM hObj hS hMaps,?_,?_⟩
  · intro r s Or Os z a hr hs hz ha
    have hrI := (hpres.2.2.2.1 r).mp ((hObj r Or).mp hr).1
    have hsI := (hpres.2.2.2.1 s).mp ((hObj s Os).mp hs).1
    have hsr := map_order hS hMaps hz ha
    obtain ⟨Ar,Hr,Xr,Qr,pr,As,Hs,Xs,Qs,ps,f,hDr,hDs,hf,hR,hMap,hA⟩ := map_data hM hObj hMaps hr hs hz ha
    obtain ⟨hAr,hHr,hXr,_,_,hPr,_⟩ := hDr
    obtain ⟨_,_,_,_,_,hPs,_⟩ := hDs
    exact ForcingEligibleLaws.restrict_injective hM hChoice env rho G F mul
      hw hMu hI hD hMergers hRow hm hpres hG hFilter hrI hsI hsr hAr hHr hg hXr hPr hPs hf hR hA hMap
  · intro p s0 s1 v OP O0 O1 OV z0 z1 zk0 zk1 a0 a1 b0 b1 x0 x1 y hp h0 h1 hv hz0 hz1 hzk0 hzk1 ha0 ha1 hb0 hb1 hInter he0 he1
    have hpI := (hpres.2.2.2.1 p).mp ((hObj p OP).mp hp).1
    have h0I := (hpres.2.2.2.1 s0).mp ((hObj s0 O0).mp h0).1
    have h1I := (hpres.2.2.2.1 s1).mp ((hObj s1 O1).mp h1).1
    have hvI := (hpres.2.2.2.1 v).mp ((hObj v OV).mp hv).1
    have hv0 := map_order hS hMaps hz0 ha0
    have hv1 := map_order hS hMaps hz1 ha1
    have hs0p := map_order hS hMaps hzk0 hb0
    have hs1p := map_order hS hMaps hzk1 hb1
    obtain ⟨A0,H0,X0,Q0,pr0,Av,Hv,Xv,Qv,prv,f0,hD0,hDv,_,hF0,_,hA0⟩ := map_data hM hObj hMaps h0 hv hz0 ha0
    obtain ⟨A1,H1,X1,Q1,pr1,Av',Hv',Xv',Qv',prv',f1,hD1,hDv',_,hF1,_,hA1⟩ := map_data hM hObj hMaps h1 hv hz1 ha1
    obtain ⟨Ap,Hp,XP,QP,prP,A0',H0',X0',Q0',pr0',k0,hDP,hD0',_,hK0,_,hB0⟩ := map_data hM hObj hMaps hp h0 hzk0 hb0
    obtain ⟨Ap',Hp',XP',QP',prP',A1',H1',X1',Q1',pr1',k1,hDP',hD1',_,hK1,_,hB1⟩ := map_data hM hObj hMaps hp h1 hzk1 hb1
    obtain ⟨rfl,rfl,rfl,rfl,rfl,_⟩ := ForcingEligibleFamily.data_unique hM hDv hDv'
    obtain ⟨rfl,rfl,rfl,rfl,rfl,_⟩ := ForcingEligibleFamily.data_unique hM hD0 hD0'
    obtain ⟨rfl,rfl,rfl,rfl,rfl,_⟩ := ForcingEligibleFamily.data_unique hM hD1 hD1'
    obtain ⟨rfl,rfl,rfl,rfl,rfl,_⟩ := ForcingEligibleFamily.data_unique hM hDP hDP'
    obtain ⟨hA0r,hH0,hX0,hpr0,_,hPr0,hO0⟩ := hD0
    obtain ⟨hA1r,hH1,hX1,hpr1,_,hPr1,hO1⟩ := hD1
    obtain ⟨hApr,hHp,hXP,_,hQP,hPrP,hOP⟩ := hDP
    obtain ⟨_,_,_,_,_,hPrv,_⟩ := hDv
    exact ForcingEligibleIntersection.intersection hM hChoice env rho G F mul
      hw hMu hI hD hMergers hRow hm hpres hG hFilter hpI h0I h1I hvI hs0p hs1p hInter hv0 hv1
      hA0r hA1r hApr hH0 hH1 hHp hc ht hLabels hBound hg hX0 hX1 hXP hpr0 hpr1 hQP
      hPr0 hPr1 hPrP hPrv hF0 hF1 hK0 hK1 hq hRangeQ hFixQ hE hO0 hO1 hOP hA0 hA1 hB0 hB1 he0 he1

def identity {m : Nat} (objects maps : Fin m) : Project.Formula 1 m :=
  let up : Fin m → Fin (m+4) := fun i => i.succ.succ.succ.succ
  let r : Fin (m+4) := 3
  let Or : Fin (m+4) := 2
  let z : Fin (m+4) := 1
  let a : Fin (m+4) := 0
  (.forallE (.forallE (.forallE (.forallE (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge (up objects) r Or)) (.imp (ProjectSyntax.encode id (PairSyntax.ordered z r r)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge (up maps) z a)) (ProjectSyntax.encode id (ForcingConditionGraphs.identityGraph Or a)))))))))

theorem identity_freeClosed {m : Nat} (objects maps : Fin m) : (identity objects maps).FreeClosed := by
  simp -implicitDefEqProofs [identity,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed]

theorem identity_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (objects maps : Fin m) :
    Project.Formula.satisfies env (identity objects maps) ↔
      Identity (env.bound objects) (env.bound maps) := by
  simp only [identity,Identity,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,
    KuratowskiZF.source_code,ForcingConditionGraphs.identityGraph_semantics (M := M)]
  rfl

def composition {m : Nat} (objects maps : Fin m) : Project.Formula 1 m :=
  let up : Fin m → Fin (m+12) := fun i => i.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  let r : Fin (m+12) := 11
  let s : Fin (m+12) := 10
  let t : Fin (m+12) := 9
  let Or : Fin (m+12) := 8
  let Os : Fin (m+12) := 7
  let Ot : Fin (m+12) := 6
  let z01 : Fin (m+12) := 5
  let z12 : Fin (m+12) := 4
  let z02 : Fin (m+12) := 3
  let a01 : Fin (m+12) := 2
  let a12 : Fin (m+12) := 1
  let a02 : Fin (m+12) := 0
  (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge (up objects) r Or)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge (up objects) s Os)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge (up objects) t Ot)) (.imp (ProjectSyntax.encode id (PairSyntax.ordered z01 r s)) (.imp (ProjectSyntax.encode id (PairSyntax.ordered z12 s t)) (.imp (ProjectSyntax.encode id (PairSyntax.ordered z02 r t)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge (up maps) z01 a01)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge (up maps) z12 a12)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge (up maps) z02 a02)) (ProjectSyntax.encode id (ForcingConditionGraphs.compositionGraph Or a12 a01 a02)))))))))))))))))))))))

theorem composition_freeClosed {m : Nat} (objects maps : Fin m) : (composition objects maps).FreeClosed := by
  simp -implicitDefEqProofs [composition,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed]

theorem composition_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (objects maps : Fin m) :
    Project.Formula.satisfies env (composition objects maps) ↔
      Composition (env.bound objects) (env.bound maps) := by
  simp only [composition,Composition,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,
    KuratowskiZF.source_code,ForcingConditionGraphs.compositionGraph_semantics (M := M)]
  rfl

def injective {m : Nat} (objects maps : Fin m) : Project.Formula 1 m :=
  let up : Fin m → Fin (m+6) := fun i => i.succ.succ.succ.succ.succ.succ
  let r : Fin (m+6) := 5
  let s : Fin (m+6) := 4
  let Or : Fin (m+6) := 3
  let Os : Fin (m+6) := 2
  let z : Fin (m+6) := 1
  let a : Fin (m+6) := 0
  (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge (up objects) r Or)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge (up objects) s Os)) (.imp (ProjectSyntax.encode id (PairSyntax.ordered z r s)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge (up maps) z a)) (ProjectSyntax.encode id (Source.SetLanguage.injection a Or Os))))))))))))

theorem injective_freeClosed {m : Nat} (objects maps : Fin m) : (injective objects maps).FreeClosed := by
  simp -implicitDefEqProofs [injective,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed]

theorem injective_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (objects maps : Fin m) :
    Project.Formula.satisfies env (injective objects maps) ↔
      Injective (env.bound objects) (env.bound maps) := by
  simp only [injective,Injective,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,
    KuratowskiZF.source_code,ForcingSupportSize.injection_semantics (M := M)]
  rfl

def intersection {m : Nat} (D objects maps : Fin m) : Project.Formula 1 m :=
  let up : Fin m → Fin (m+19) := fun i => i.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  let p : Fin (m+19) := 18
  let s0 : Fin (m+19) := 17
  let s1 : Fin (m+19) := 16
  let v : Fin (m+19) := 15
  let OP : Fin (m+19) := 14
  let O0 : Fin (m+19) := 13
  let O1 : Fin (m+19) := 12
  let OV : Fin (m+19) := 11
  let z0 : Fin (m+19) := 10
  let z1 : Fin (m+19) := 9
  let zk0 : Fin (m+19) := 8
  let zk1 : Fin (m+19) := 7
  let a0 : Fin (m+19) := 6
  let a1 : Fin (m+19) := 5
  let b0 : Fin (m+19) := 4
  let b1 : Fin (m+19) := 3
  let x0 : Fin (m+19) := 2
  let x1 : Fin (m+19) := 1
  let y : Fin (m+19) := 0
  (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge (up objects) p OP)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge (up objects) s0 O0)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge (up objects) s1 O1)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge (up objects) v OV)) (.imp (ProjectSyntax.encode id (PairSyntax.ordered z0 s0 v)) (.imp (ProjectSyntax.encode id (PairSyntax.ordered z1 s1 v)) (.imp (ProjectSyntax.encode id (PairSyntax.ordered zk0 p s0)) (.imp (ProjectSyntax.encode id (PairSyntax.ordered zk1 p s1)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge (up maps) z0 a0)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge (up maps) z1 a1)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge (up maps) zk0 b0)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge (up maps) zk1 b1)) (.imp (ConstructionDiagramPlacements.rangeIntersection (up D) s0 s1 p) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge a0 x0 y)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge a1 x1 y)) (ProjectSyntax.encode id (ForcingLocalIntersection.result OP b0 b1 x0 x1))))))))))))))))))))))))))))))))))))

theorem intersection_freeClosed {m : Nat} (D objects maps : Fin m) : (intersection D objects maps).FreeClosed := by
  simp -implicitDefEqProofs [intersection,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,ConstructionDiagramPlacements.rangeIntersection_freeClosed]

theorem intersection_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (D objects maps : Fin m) :
    Project.Formula.satisfies env (intersection D objects maps) ↔
      Intersection (env.bound D) (env.bound objects) (env.bound maps) := by
  simp only [intersection,Intersection,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,
    KuratowskiZF.source_code,ConstructionDiagramPlacements.rangeIntersection_semantics hM,ForcingLocalIntersection.result_semantics (M := M)]
  rfl

def system {m : Nat} (D objects maps : Fin m) : Project.Formula 1 m :=
  .conj (ProjectSyntax.encode id (ForcingEligibleMapFamily.compatible objects maps))
    (.conj (identity objects maps) (.conj (composition objects maps)
      (.conj (injective objects maps) (intersection D objects maps))))

theorem system_freeClosed {m : Nat} (D objects maps : Fin m) : (system D objects maps).FreeClosed := by
  simp -implicitDefEqProofs [system,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
    identity_freeClosed,composition_freeClosed,injective_freeClosed,intersection_freeClosed]

theorem system_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (D objects maps : Fin m) :
    Project.Formula.satisfies env (system D objects maps) ↔
      System (env.bound D) (env.bound objects) (env.bound maps) := by
  simp only [system,System,Project.Formula.satisfies_conj_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingEligibleMapFamily.compatible_semantics (M := M),
    identity_semantics hM,composition_semantics hM,injective_semantics hM,intersection_semantics hM]
  rfl

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
      (.imp (Project.Formula.isOmega (.bound w)) (.imp (Project.Formula.isInfiniteCardinal PureKuratowskiProject.convention (.bound w) (.bound mu)) (.imp (ConstructionSaturationIndex.hartogs mu I) (.imp (ProjectSyntax.encode id (ForcingSupportSize.small (rho 0) mu)) (.imp (ConstructionSaturationMergers.allMergers w history kappa) (.imp (ConstructionTowerHistory.row history kappa (rho 0) mul e mark H C incoming base kappa) (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid (rho 0) mul e)) (.imp (ProjectSyntax.encode id (ForcingProductFamily.presentation (rho 0) I K B w (rho 1) (rho 2) (rho 3) (rho 4) (rho 5) (rho 6))) (.imp (ProjectSyntax.encode id (ForcingLabelPermutations.carrier I G)) (.imp (ProjectSyntax.encode id (ForcingSupportFilter.filter I G mu F)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.functionOn c K)) (.imp (ProjectSyntax.encode id (ForcingWithTopCarrier.empty t)) (.imp (ProjectSyntax.encode id (ForcingLabelSet.labelSet (rho 6) I K c t b labels)) (.imp (ProjectSyntax.encode id (ForcingLabelBound.labelBound (rho 6) I K c t b nameBound)) (.imp (ProjectSyntax.encode id (ForcingLocalAtomic.cohenFilter (rho 3) g)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.injection q (rho 0) I)) (.imp (ProjectSyntax.encode id (ForcingSupportedNames.range (rho 0) q Aq)) (.imp (ProjectSyntax.encode id (ForcingLabelPermutations.fixing G Aq fixingQ)) (.imp (ProjectSyntax.encode id (ForcingEquivariantMix.fixedAll rho fixingQ E)) (.existsE (.existsE (.existsE (.existsE (.existsE (.conj (ProjectSyntax.encode id (Source.SetLanguage.mapsTo objects (up (rho 4)) objImage)) (.conj (ProjectSyntax.encode id (ForcingEligibleFamily.family (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) up (fun i => up (rho i)) (up G) (up F) (up mul) (up g) (up q) (up nameBound) (up labels) (up E) (up (rho 4)) objects)) (.conj (ProjectSyntax.encode id (ForcingEligibleMapFamily.arrows (up (rho 0)) (up mul) (up (rho 4)) S)) (.conj (ProjectSyntax.encode id (Source.SetLanguage.mapsTo maps S mapImage)) (.conj (ProjectSyntax.encode id (ForcingEligibleMapFamily.family (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) up (fun i => up (rho i)) (up G) (up F) (up mul) (up g) (up q) (up nameBound) (up labels) (up E) S maps)) (system (up (rho 0)) objects maps))))))))))))))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,
      Project.Formula.isOmega,Project.Formula.isInfiniteCardinal,
      ConstructionSaturationIndex.hartogs_freeClosed,ProjectSyntax.freeClosed,
      ConstructionSaturationMergers.allMergers_freeClosed,ConstructionTowerHistory.row_freeClosed,
      system_freeClosed]

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
    system_semantics hM,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),Project.Term.eval_bound]
  intro hw hMu hI hD hMergers hRow hm hp hG hFilter hc ht hLabels hBound hg hq hRangeQ hFixQ hE
  obtain ⟨objImage,objects,hObjMap,hObj⟩ := ForcingEligibleFamily.exists_family hM
    (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) bound rho G F mul g q nameBound labels E I (rho 4)
    hp.2.2.2.1
  obtain ⟨S,hS⟩ := ForcingEligibleMapFamily.exists_arrows hM bound (rho 0) mul (rho 4)
  obtain ⟨mapImage,maps,hMap,hMaps⟩ := ForcingEligibleMapFamily.exists_family hM bound rho G F mul
    I K B w e g q nameBound labels E S hm hp hg hS
  exact ⟨objImage,objects,S,mapImage,maps,hObjMap,hObj,hS,hMap,hMaps,
    system_of_families hM hChoice bound rho G F mul
      hw hMu hI hD hMergers hRow hm hp hG hFilter hc ht hLabels hBound hg hq hRangeQ hFixQ hE hObj hS hMaps⟩

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


end PPAC.Migration.ForcingEligibleSystem
