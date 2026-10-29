/- Pinned AvailableRecords.eligibleSystem.restrict:273-274 over ALL internal
comparable diagram pairs. Use native Cartesian product, Separation, functional
image and set-function constructors; consume the existing actual quotient and
Obj restriction constructors. No external enumeration or choice of maps. -/
import PPAC.Migration.ForcingEligibleFamily

namespace PPAC.Migration.ForcingEligibleMapFamily
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open Source (Formula)
open ForcingSupportSize (MapsTo Injection)
open ForcingEligibleFamily (Data Row)
open ForcingProductSymmetry (orderFormula)
open ReplacementPredicates (paramsUp)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def Arrow (D mul diagrams z : M.Carrier .set) : Prop :=
  ∃ r s, (Project.FirstOrderSemantics.reduct M).mem r diagrams ∧
    (Project.FirstOrderSemantics.reduct M).mem s diagrams ∧
    ForcingDiagramOrder.Le D mul s r ∧ PureKuratowski.Code M z r s

def arrow {m : Nat} (D mul diagrams z : Fin m) : Formula m :=
  .ex (.ex ((Formula.mem (Fin.last m).castSucc diagrams.castSucc.castSucc).conj
    ((Formula.mem (Fin.last (m+1)) diagrams.castSucc.castSucc).conj
      ((ForcingDiagramOrder.le D.castSucc.castSucc mul.castSucc.castSucc
        (Fin.last (m+1)) (Fin.last m).castSucc).conj
        (PairSyntax.ordered z.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)))))))

theorem arrow_semantics {m : Nat} (env : Fin m → M.Carrier .set) (D mul diagrams z : Fin m) :
    Formula.Realize (Project.FirstOrderSemantics.reduct M).mem env (arrow D mul diagrams z) ↔
      Arrow (env D) (env mul) (env diagrams) (env z) := by
  simp only [arrow,Arrow,Formula.Realize,ForcingDiagramOrder.le_semantics (M := M),
    KuratowskiZF.source_code,Fin.lastCases_last,Fin.lastCases_castSucc]

def Arrows (D mul diagrams S : M.Carrier .set) : Prop :=
  ∀ z, (Project.FirstOrderSemantics.reduct M).mem z S ↔ Arrow D mul diagrams z

def arrows {m : Nat} (D mul diagrams S : Fin m) : Formula m :=
  .all ((Formula.mem (Fin.last m) S.castSucc).iff
    (arrow D.castSucc mul.castSucc diagrams.castSucc (Fin.last m)))

theorem arrows_semantics {m : Nat} (env : Fin m → M.Carrier .set) (D mul diagrams S : Fin m) :
    Formula.Realize (Project.FirstOrderSemantics.reduct M).mem env (arrows D mul diagrams S) ↔
      Arrows (env D) (env mul) (env diagrams) (env S) := by
  simp only [arrows,Arrows,Source.Formula.iff,Formula.Realize,arrow_semantics (M := M),
    Fin.lastCases_last,Fin.lastCases_castSucc]
  exact ⟨fun h z => ⟨(h z).1,(h z).2⟩,fun h z => ⟨(h z).mp,(h z).mpr⟩⟩

theorem exists_arrows (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (D mul diagrams : Fin k) :
    ∃ S, Arrows (env D) (env mul) (env diagrams) S := by
  obtain ⟨C,hC⟩ := ForcingCohenCoordinates.exists_cartesian hM (env diagrams) (env diagrams)
  let test := arrow D.castSucc mul.castSucc diagrams.castSucc (Fin.last k)
  have sep := (GodelDefOutput.separation_semantics (Project.FirstOrderSemantics.reduct M).mem test).mp
    ((Translation.realizes_sentence M _).mp ((SeparationSyntax.source_separation test).semantically_entails M hM))
  obtain ⟨S,hS⟩ := sep env C
  have ht : ∀ z, Formula.Realize (Project.FirstOrderSemantics.reduct M).mem (Fin.lastCases z env) test ↔
      Arrow (env D) (env mul) (env diagrams) z := by
    intro z
    simpa only [test,Fin.lastCases_last,Fin.lastCases_castSucc] using
      arrow_semantics (M := M) (Fin.lastCases z env) D.castSucc mul.castSucc diagrams.castSucc (Fin.last k)
  refine ⟨S,fun z => (hS z).trans ?_⟩
  constructor
  · exact fun hz => (ht z).mp hz.2
  · intro hz
    obtain ⟨r,s,hr,hs,hsr,hc⟩ := hz
    exact ⟨(hC z).mpr ⟨r,hr,s,hs,hc⟩,(ht z).mpr ⟨r,s,hr,hs,hsr,hc⟩⟩

def MapRow {k : Nat} (R : Formula (k+2)) (Hdom : Formula (k+1))
    (env : Fin k → M.Carrier .set) (v : Fin 7 → M.Carrier .set)
    (G F mul g q nameBound labels E z a : M.Carrier .set) : Prop :=
  ∃ r s Ar Hr Xr Qr pr Or As Hs Xs Qs ps Os f,
    PureKuratowski.Code M z r s ∧
    Data R Hdom env v G F mul g q nameBound labels E r Ar Hr Xr Qr pr Or ∧
    Data R Hdom env v G F mul g q nameBound labels E s As Hs Xs Qs ps Os ∧
    MapsTo Qr Qs f ∧ ForcingLocalRestriction.Restriction pr ps f ∧
    MapsTo Or Os a ∧ ForcingEligibleRestriction.Restricts a f Or

def mapRow {k m : Nat} (R : Formula (k+2)) (Hdom : Formula (k+1))
    (base : Fin k → Fin m) (rho : Fin 7 → Fin m)
    (G F mul g q nameBound labels E z a : Fin m) : Formula m :=
  let up : Fin m → Fin (m+15) := fun i => i.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc
  let r := (Fin.last m).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc
  let s := (Fin.last (m+1)).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc
  let Ar := (Fin.last (m+2)).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc
  let Hr := (Fin.last (m+3)).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc
  let Xr := (Fin.last (m+4)).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc
  let Qr := (Fin.last (m+5)).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc
  let pr := (Fin.last (m+6)).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc
  let Or := (Fin.last (m+7)).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc
  let As := (Fin.last (m+8)).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc
  let Hs := (Fin.last (m+9)).castSucc.castSucc.castSucc.castSucc.castSucc
  let Xs := (Fin.last (m+10)).castSucc.castSucc.castSucc.castSucc
  let Qs := (Fin.last (m+11)).castSucc.castSucc.castSucc
  let ps := (Fin.last (m+12)).castSucc.castSucc
  let Os := (Fin.last (m+13)).castSucc
  let f := (Fin.last (m+14))
  .ex (.ex (.ex (.ex (.ex (.ex (.ex (.ex (.ex (.ex (.ex (.ex (.ex (.ex (.ex ((PairSyntax.ordered (up z) r s).conj ((ForcingEligibleFamily.data R Hdom (fun j => up (base j)) (fun j => up (rho j)) (up G) (up F) (up mul) (up g) (up q) (up nameBound) (up labels) (up E) r Ar Hr Xr Qr pr Or).conj ((ForcingEligibleFamily.data R Hdom (fun j => up (base j)) (fun j => up (rho j)) (up G) (up F) (up mul) (up g) (up q) (up nameBound) (up labels) (up E) s As Hs Xs Qs ps Os).conj ((Source.SetLanguage.mapsTo f Qr Qs).conj ((ForcingLocalRestriction.restriction pr ps f).conj ((Source.SetLanguage.mapsTo (up a) Or Os).conj (RestrictionSyntax.edgeLaw (up a) f Or)))))))))))))))))))))

theorem mapRow_semantics {k m : Nat} (env : Fin m → M.Carrier .set)
    (R : Formula (k+2)) (Hdom : Formula (k+1)) (base : Fin k → Fin m) (rho : Fin 7 → Fin m)
    (G F mul g q nameBound labels E z a : Fin m) :
    Formula.Realize (Project.FirstOrderSemantics.reduct M).mem env
      (mapRow R Hdom base rho G F mul g q nameBound labels E z a) ↔
    MapRow R Hdom (fun j => env (base j)) (fun j => env (rho j))
      (env G) (env F) (env mul) (env g) (env q) (env nameBound) (env labels) (env E) (env z) (env a) := by
  simp only [mapRow,MapRow,Formula.Realize,KuratowskiZF.source_code,
    ForcingEligibleFamily.data_semantics (M := M),ForcingSupportSize.mapsTo_semantics (M := M),
    ForcingLocalRestriction.restriction_semantics (M := M),ForcingEligibleRestriction.edgeLaw_semantics (M := M),
    Fin.lastCases_last,Fin.lastCases_castSucc]
  rfl

theorem exists_map_row (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (G F mul : Fin k)
    {I K B w e g q nameBound labels E r s z : M.Carrier .set}
    (hm : ForcingDiagramPoset.LeftCancelMonoid (env (rho 0)) (env mul) e)
    (hp : ForcingProductFamily.Presentation (env (rho 0)) I K B w
      (env (rho 1)) (env (rho 2)) (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hg : ForcingLocalAtomic.CohenFilter (env (rho 3)) g)
    (hr : Injection (env (rho 0)) I r) (hs : Injection (env (rho 0)) I s)
    (hsr : ForcingDiagramOrder.Le (env (rho 0)) (env mul) s r) (hz : PureKuratowski.Code M z r s) :
    ∃ a, MapRow (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) env
      (fun i => env (rho i)) (env G) (env F) (env mul) g q nameBound labels E z a := by
  obtain ⟨Or,Ar,Hr,Xr,Qr,pr,hDr⟩ := ForcingEligibleFamily.exists_row hM (orderFormula (rho 0) mul)
    (ForcingPairUnion.domain rho G F) env (fun i => env (rho i)) (env G) (env F) (env mul)
    g q nameBound labels E hr
  obtain ⟨Os,As,Hs,Xs,Qs,ps,hDs⟩ := ForcingEligibleFamily.exists_row hM (orderFormula (rho 0) mul)
    (ForcingPairUnion.domain rho G F) env (fun i => env (rho i)) (env G) (env F) (env mul)
    g q nameBound labels E hs
  obtain ⟨hAr,hHr,hXr,hpr,hQr,hPr,hOr⟩ := hDr
  obtain ⟨hAs,hHs,hXs,hps,hQs,hPs,hOs⟩ := hDs
  obtain ⟨f,hf,hR⟩ := ForcingLocalRestriction.actual_restriction hM env rho mul hm hp hg hr hs hsr
    hAr hAs hHr hHs hXr hXs hpr hps hQr hPr hPs
  obtain ⟨a,ha,hA⟩ := ForcingEligibleRestriction.exists_restriction hM env rho G F mul
    hm hp hg hr hs hsr hPr hf hR hOr hOs
  exact ⟨a,r,s,Ar,Hr,Xr,Qr,pr,Or,As,Hs,Xs,Qs,ps,Os,f,hz,
    ⟨hAr,hHr,hXr,hpr,hQr,hPr,hOr⟩,⟨hAs,hHs,hXs,hps,hQs,hPs,hOs⟩,hf,hR,ha,hA⟩

theorem map_row_unique (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    {R : Formula (k+2)} {Hdom : Formula (k+1)} {env : Fin k → M.Carrier .set}
    {v : Fin 7 → M.Carrier .set} {G F mul g q nameBound labels E z a b : M.Carrier .set}
    (ha : MapRow R Hdom env v G F mul g q nameBound labels E z a)
    (hb : MapRow R Hdom env v G F mul g q nameBound labels E z b) : a = b := by
  obtain ⟨r,s,Ar,Hr,Xr,Qr,pr,Or,As,Hs,Xs,Qs,ps,Os,f,hz,hDr,hDs,hf,hR,ha,hA⟩ := ha
  obtain ⟨r',s',Ar',Hr',Xr',Qr',pr',Or',As',Hs',Xs',Qs',ps',Os',f',hz',hDr',hDs',hf',hR',hb,hB⟩ := hb
  obtain ⟨rfl,rfl⟩ := PureKuratowski.code_injective hz hz'
  obtain ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩ := ForcingEligibleFamily.data_unique hM hDr hDr'
  obtain ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩ := ForcingEligibleFamily.data_unique hM hDs hDs'
  have hff : f = f' := SetTheory.Structure.IsSetRelation.eq_of_pairMember_iff
    (ModelTransfer.extensionality hM)
    ((ForcingSupportSize.native_mapsTo hM _ _ f).mp hf).1.1
    ((ForcingSupportSize.native_mapsTo hM _ _ f').mp hf').1.1
    (fun x y => (hR x y).trans (hR' x y).symm)
  subst f'
  exact SetTheory.Structure.IsSetRelation.eq_of_pairMember_iff (ModelTransfer.extensionality hM)
    ((ForcingSupportSize.native_mapsTo hM _ _ a).mp ha).1.1
    ((ForcingSupportSize.native_mapsTo hM _ _ b).mp hb).1.1
    (fun x y => (hA x y).trans (hB x y).symm)

def Family {k : Nat} (R : Formula (k+2)) (Hdom : Formula (k+1))
    (env : Fin k → M.Carrier .set) (v : Fin 7 → M.Carrier .set)
    (G F mul g q nameBound labels E S maps : M.Carrier .set) : Prop :=
  ∀ z a, PureKuratowski.PairMember M z a maps ↔
    (Project.FirstOrderSemantics.reduct M).mem z S ∧
      MapRow R Hdom env v G F mul g q nameBound labels E z a

def family {k m : Nat} (R : Formula (k+2)) (Hdom : Formula (k+1))
    (base : Fin k → Fin m) (rho : Fin 7 → Fin m)
    (G F mul g q nameBound labels E S maps : Fin m) : Formula m :=
  .all (.all ((Source.SetLanguage.edge maps.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))).iff
    ((Formula.mem (Fin.last m).castSucc S.castSucc.castSucc).conj
      (mapRow R Hdom (paramsUp (paramsUp base)) (paramsUp (paramsUp rho)) G.castSucc.castSucc
        F.castSucc.castSucc mul.castSucc.castSucc g.castSucc.castSucc q.castSucc.castSucc
        nameBound.castSucc.castSucc labels.castSucc.castSucc E.castSucc.castSucc
        (Fin.last m).castSucc (Fin.last (m+1))))))

theorem family_semantics {k m : Nat} (env : Fin m → M.Carrier .set)
    (R : Formula (k+2)) (Hdom : Formula (k+1)) (base : Fin k → Fin m) (rho : Fin 7 → Fin m)
    (G F mul g q nameBound labels E S maps : Fin m) :
    Formula.Realize (Project.FirstOrderSemantics.reduct M).mem env
      (family R Hdom base rho G F mul g q nameBound labels E S maps) ↔
    Family R Hdom (fun j => env (base j)) (fun j => env (rho j))
      (env G) (env F) (env mul) (env g) (env q) (env nameBound) (env labels) (env E) (env S) (env maps) := by
  simp only [family,Family,Source.Formula.iff,Formula.Realize,KuratowskiZF.source_edge,
    mapRow_semantics (M := M),paramsUp,Fin.lastCases_last,Fin.lastCases_castSucc]
  exact ⟨fun h z a => ⟨(h z a).1,(h z a).2⟩,fun h z a => ⟨(h z a).mp,(h z a).mpr⟩⟩

theorem exists_family_at_filter (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (G F mul : Fin k)
    (I K B w e q nameBound labels E : Fin k) (g S : M.Carrier .set)
    (hm : ForcingDiagramPoset.LeftCancelMonoid (env (rho 0)) (env mul) (env e))
    (hp : ForcingProductFamily.Presentation (env (rho 0)) (env I) (env K) (env B) (env w)
      (env (rho 1)) (env (rho 2)) (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hg : ForcingLocalAtomic.CohenFilter (env (rho 3)) g)
    (hS : Arrows (env (rho 0)) (env mul) (env (rho 4)) S) :
    ∃ image maps, MapsTo S image maps ∧
      Family (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) env (fun j => env (rho j))
        (env G) (env F) (env mul) g (env q) (env nameBound) (env labels) (env E) S maps := by
  let params : Fin (k+1) → M.Carrier .set := Fin.lastCases g env
  let up : Fin (k+1) → Fin (k+1+2) := fun i => i.castSucc.castSucc
  let R := orderFormula (rho 0) mul
  let Hdom := ForcingPairUnion.domain rho G F
  let query := mapRow R Hdom (fun j => up j.castSucc) (fun j => up (rho j).castSucc)
    (up G.castSucc) (up F.castSucc) (up mul.castSucc) (up (Fin.last k))
    (up q.castSucc) (up nameBound.castSucc) (up labels.castSucc) (up E.castSucc)
    (Fin.last (k+1)).castSucc (Fin.last (k+1+1))
  let penv : SetTheory.Env (Project.FirstOrderSemantics.reduct M) (k+1) :=
    { bound := fun i => params i.rev, free := fun _ => S }
  have hRel : ∀ z a, (ProjectSyntax.binary query).denote penv z a ↔
      MapRow R Hdom env (fun j => env (rho j)) (env G) (env F) (env mul) g (env q)
        (env nameBound) (env labels) (env E) z a := by
    intro z a
    rw [ForcingMapConditions.binary_semantics hM query params S z a]
    simp only [ForcingMapConditions.MapRel,query,mapRow_semantics (M := M),up,params,
      Fin.lastCases_last,Fin.lastCases_castSucc]
  have ht : ∀ z, (Project.FirstOrderSemantics.reduct M).mem z S →
      ∃ a, (ProjectSyntax.binary query).denote penv z a := by
    intro z hz
    obtain ⟨r,s,hr,hs,hsr,hcode⟩ := (hS z).mp hz
    obtain ⟨a,ha⟩ := exists_map_row hM env rho G F mul hm hp hg
      ((hp.2.2.2.1 r).mp hr) ((hp.2.2.2.1 s).mp hs) hsr hcode
    exact ⟨a,(hRel z a).mpr ha⟩
  have hu : ∀ z a b, (ProjectSyntax.binary query).denote penv z a →
      (ProjectSyntax.binary query).denote penv z b → a = b := by
    intro z a b ha hb
    exact map_row_unique hM ((hRel z a).mp ha) ((hRel z b).mp hb)
  obtain ⟨image,hImage⟩ := ZF.exists_functionalImage (ModelTransfer.project_models_iff.mp hM)
    (ProjectSyntax.binary query) penv S ht hu
  obtain ⟨maps,hMaps,hEdge⟩ := ZF.exists_setFunctionFromTo_of_denote (ModelTransfer.project_models_iff.mp hM)
    (KuratowskiZF.interpretation hM) (ProjectSyntax.binary query) penv
    ht (fun z _ a b ha hb => hu z a b ha hb)
    (fun z a hz ha => (hImage a).mpr ⟨z,hz,ha⟩)
  exact ⟨image,maps,(ForcingSupportSize.native_mapsTo hM S image maps).mpr hMaps,
    fun z a => (hEdge z a).trans (and_congr Iff.rfl (hRel z a))⟩

theorem exists_family (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (G F mul : Fin k)
    (I K B w e g q nameBound labels E : Fin k) (S : M.Carrier .set)
    (hm : ForcingDiagramPoset.LeftCancelMonoid (env (rho 0)) (env mul) (env e))
    (hp : ForcingProductFamily.Presentation (env (rho 0)) (env I) (env K) (env B) (env w)
      (env (rho 1)) (env (rho 2)) (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hg : ForcingLocalAtomic.CohenFilter (env (rho 3)) (env g))
    (hS : Arrows (env (rho 0)) (env mul) (env (rho 4)) S) :
    ∃ image maps, MapsTo S image maps ∧
      Family (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) env (fun j => env (rho j))
        (env G) (env F) (env mul) (env g) (env q) (env nameBound) (env labels) (env E) S maps := by
  exact exists_family_at_filter hM env rho G F mul I K B w e q nameBound labels E (env g) S hm hp hg hS

def Compatible (objects maps : M.Carrier .set) : Prop :=
  ∀ r s Or Os z a, PureKuratowski.PairMember M r Or objects →
    PureKuratowski.PairMember M s Os objects → PureKuratowski.Code M z r s →
    PureKuratowski.PairMember M z a maps → MapsTo Or Os a

def compatible {m : Nat} (objects maps : Fin m) : Formula m :=
  let up : Fin m → Fin (m+6) := fun i => i.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc
  let r := (Fin.last m).castSucc.castSucc.castSucc.castSucc.castSucc
  let s := (Fin.last (m+1)).castSucc.castSucc.castSucc.castSucc
  let Or := (Fin.last (m+2)).castSucc.castSucc.castSucc
  let Os := (Fin.last (m+3)).castSucc.castSucc
  let z := (Fin.last (m+4)).castSucc
  let a := Fin.last (m+5)
  .all (.all (.all (.all (.all (.all ((Source.SetLanguage.edge (up objects) r Or).imp
    ((Source.SetLanguage.edge (up objects) s Os).imp ((PairSyntax.ordered z r s).imp
      ((Source.SetLanguage.edge (up maps) z a).imp (Source.SetLanguage.mapsTo a Or Os))))))))))

theorem compatible_semantics {m : Nat} (env : Fin m → M.Carrier .set) (objects maps : Fin m) :
    Formula.Realize (Project.FirstOrderSemantics.reduct M).mem env (compatible objects maps) ↔
      Compatible (env objects) (env maps) := by
  simp only [compatible,Compatible,Formula.Realize,KuratowskiZF.source_edge,KuratowskiZF.source_code,
    ForcingSupportSize.mapsTo_semantics (M := M),Fin.lastCases_last,Fin.lastCases_castSucc]
  rfl

theorem compatible_of_families (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    {R : Formula (k+2)} {Hdom : Formula (k+1)} {env : Fin k → M.Carrier .set}
    {v : Fin 7 → M.Carrier .set} {G F mul g q nameBound labels E diagrams objects S maps : M.Carrier .set}
    (hObj : ForcingEligibleFamily.Family R Hdom env v G F mul g q nameBound labels E diagrams objects)
    (hMaps : Family R Hdom env v G F mul g q nameBound labels E S maps) : Compatible objects maps := by
  intro r s Or Os z a hr hs hz ha
  have hOr := ((hObj r Or).mp hr).2
  have hOs := ((hObj s Os).mp hs).2
  obtain ⟨r',s',Ar,Hr,Xr,Qr,pr,Or',As,Hs,Xs,Qs,ps,Os',f,hz',hDr,hDs,_,_,hMap,_⟩ := ((hMaps z a).mp ha).2
  obtain ⟨rfl,rfl⟩ := PureKuratowski.code_injective hz hz'
  have her := ForcingEligibleFamily.row_unique hM hOr ⟨Ar,Hr,Xr,Qr,pr,hDr⟩
  have hes := ForcingEligibleFamily.row_unique hM hOs ⟨As,Hs,Xs,Qs,ps,hDs⟩
  simpa only [her,hes] using hMap

def constructionSentence {k : Nat} (rho : Fin 7 → Fin k) (I K B w e G F mul g q nameBound labels E : Fin k) : Source.Sentence :=
  let up : Fin k → Fin (k+5) := fun i => i.castSucc.castSucc.castSucc.castSucc.castSucc
  let objImage := (Fin.last k).castSucc.castSucc.castSucc.castSucc
  let objects := (Fin.last (k+1)).castSucc.castSucc.castSucc
  let S := (Fin.last (k+2)).castSucc.castSucc
  let mapImage := (Fin.last (k+3)).castSucc
  let maps := (Fin.last (k+4))
  ((ForcingDiagramPoset.leftCancelMonoid (rho 0) mul e).imp ((ForcingProductFamily.presentation (rho 0) I K B w (rho 1) (rho 2) (rho 3) (rho 4) (rho 5) (rho 6)).imp ((ForcingLocalAtomic.cohenFilter (rho 3) g).imp (.ex (.ex (.ex (.ex (.ex ((Source.SetLanguage.mapsTo objects (up (rho 4)) objImage).conj ((ForcingEligibleFamily.family (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) up (fun j => up (rho j)) (up G) (up F) (up mul) (up g) (up q) (up nameBound) (up labels) (up E) (up (rho 4)) objects).conj ((arrows (up (rho 0)) (up mul) (up (rho 4)) S).conj ((Source.SetLanguage.mapsTo maps S mapImage).conj ((family (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) up (fun j => up (rho j)) (up G) (up F) (up mul) (up g) (up q) (up nameBound) (up labels) (up E) S maps).conj (compatible objects maps)))))))))))))).close

theorem construction_models {k : Nat} (rho : Fin 7 → Fin k) (I K B w e G F mul g q nameBound labels E : Fin k)
    (hM : FirstOrder.Theory.Models M nativeZF) :
    (Translation.sentence (constructionSentence rho I K B w e G F mul g q nameBound labels E)).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro env hm hp hg
  have hm := (ForcingDiagramPoset.leftCancelMonoid_semantics (M := M) env (rho 0) mul e).mp hm
  have hp := (ForcingProductFamily.presentation_semantics (M := M) env (rho 0) I K B w (rho 1) (rho 2) (rho 3) (rho 4) (rho 5) (rho 6)).mp hp
  have hg := (ForcingLocalAtomic.cohenFilter_semantics (M := M) env (rho 3) g).mp hg
  obtain ⟨objImage,objects,hObjMap,hObj⟩ := ForcingEligibleFamily.exists_family hM
    (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) env rho G F mul g q nameBound labels E I (rho 4)
    hp.2.2.2.1
  obtain ⟨S,hS⟩ := exists_arrows hM env (rho 0) mul (rho 4)
  obtain ⟨mapImage,maps,hMap,hMaps⟩ := exists_family hM env rho G F mul I K B w e g q nameBound labels E S hm hp hg hS
  have hCompatible := compatible_of_families hM hObj hMaps
  refine ⟨objImage,objects,S,mapImage,maps,?_,?_,?_,?_,?_,?_⟩
  · apply (ForcingSupportSize.mapsTo_semantics (M := M) (Fin.lastCases maps (Fin.lastCases mapImage (Fin.lastCases S (Fin.lastCases objects (Fin.lastCases objImage env)))))
      (Fin.last (k+1)).castSucc.castSucc.castSucc (rho 4).castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last k).castSucc.castSucc.castSucc.castSucc).mpr
    simpa only [Fin.lastCases_last,Fin.lastCases_castSucc] using hObjMap
  · apply (ForcingEligibleFamily.family_semantics (M := M) (Fin.lastCases maps (Fin.lastCases mapImage (Fin.lastCases S (Fin.lastCases objects (Fin.lastCases objImage env)))))
      (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) (fun i => i.castSucc.castSucc.castSucc.castSucc.castSucc) (fun j => (rho j).castSucc.castSucc.castSucc.castSucc.castSucc) (G).castSucc.castSucc.castSucc.castSucc.castSucc (F).castSucc.castSucc.castSucc.castSucc.castSucc (mul).castSucc.castSucc.castSucc.castSucc.castSucc (g).castSucc.castSucc.castSucc.castSucc.castSucc (q).castSucc.castSucc.castSucc.castSucc.castSucc (nameBound).castSucc.castSucc.castSucc.castSucc.castSucc (labels).castSucc.castSucc.castSucc.castSucc.castSucc (E).castSucc.castSucc.castSucc.castSucc.castSucc (rho 4).castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (k+1)).castSucc.castSucc.castSucc).mpr
    simpa only [Fin.lastCases_last,Fin.lastCases_castSucc] using hObj
  · apply (arrows_semantics (M := M) (Fin.lastCases maps (Fin.lastCases mapImage (Fin.lastCases S (Fin.lastCases objects (Fin.lastCases objImage env)))))
      (rho 0).castSucc.castSucc.castSucc.castSucc.castSucc (mul).castSucc.castSucc.castSucc.castSucc.castSucc (rho 4).castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (k+2)).castSucc.castSucc).mpr
    simpa only [Fin.lastCases_last,Fin.lastCases_castSucc] using hS
  · apply (ForcingSupportSize.mapsTo_semantics (M := M) (Fin.lastCases maps (Fin.lastCases mapImage (Fin.lastCases S (Fin.lastCases objects (Fin.lastCases objImage env)))))
      (Fin.last (k+4)) (Fin.last (k+2)).castSucc.castSucc (Fin.last (k+3)).castSucc).mpr
    simpa only [Fin.lastCases_last,Fin.lastCases_castSucc] using hMap
  · apply (family_semantics (M := M) (Fin.lastCases maps (Fin.lastCases mapImage (Fin.lastCases S (Fin.lastCases objects (Fin.lastCases objImage env)))))
      (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) (fun i => i.castSucc.castSucc.castSucc.castSucc.castSucc) (fun j => (rho j).castSucc.castSucc.castSucc.castSucc.castSucc) (G).castSucc.castSucc.castSucc.castSucc.castSucc (F).castSucc.castSucc.castSucc.castSucc.castSucc (mul).castSucc.castSucc.castSucc.castSucc.castSucc (g).castSucc.castSucc.castSucc.castSucc.castSucc (q).castSucc.castSucc.castSucc.castSucc.castSucc (nameBound).castSucc.castSucc.castSucc.castSucc.castSucc (labels).castSucc.castSucc.castSucc.castSucc.castSucc (E).castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (k+2)).castSucc.castSucc (Fin.last (k+4))).mpr
    simpa only [Fin.lastCases_last,Fin.lastCases_castSucc] using hMaps
  · apply (compatible_semantics (M := M) (Fin.lastCases maps (Fin.lastCases mapImage (Fin.lastCases S (Fin.lastCases objects (Fin.lastCases objImage env)))))
      (Fin.last (k+1)).castSucc.castSucc.castSucc (Fin.last (k+4))).mpr
    simpa only [Fin.lastCases_last,Fin.lastCases_castSucc] using hCompatible

theorem construction_kernel_certificate {k : Nat} (rho : Fin 7 → Fin k) (I K B w e G F mul g q nameBound labels E : Fin k) :
    FirstOrder.Derives nativeZF [] (Translation.sentence (constructionSentence rho I K B w e G F mul g q nameBound labels E)) :=
  ModelTransfer.derives (fun _ hM => construction_models rho I K B w e G F mul g q nameBound labels E hM)

end PPAC.Migration.ForcingEligibleMapFamily
