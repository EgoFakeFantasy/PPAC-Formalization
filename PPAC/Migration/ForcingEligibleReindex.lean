/- Pinned QuotientTransport.eligibleSystemTransport:309-337.
Collect the unique actual per-diagram apps with existing native Replacement.
Align all object/map rows using existing Data uniqueness, then descend the
already proved quotient restriction square to the eligible objects. -/
import PPAC.Migration.ForcingEligibleTransport
import PPAC.Migration.ForcingReindexSystem

namespace PPAC.Migration.ForcingEligibleReindex
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open Source (Formula)
open ForcingSupportSize (MapsTo Injection)
open ForcingConditionGraphs (CompositionGraph Permutation)
open ForcingEligibleFamily (Data)
open ForcingProductSymmetry (orderFormula)
open ForcingEligibleRestriction (Restricts)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 6000000
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def Row {k : Nat} (R : Formula (k+2)) (Hdom : Formula (k+1))
    (env : Fin k → M.Carrier .set) (v : Fin 7 → M.Carrier .set)
    (G F mul g gT q bound labels E pi a r b : M.Carrier .set) : Prop :=
  ∃ rT Ar Hr X Q pr O AT HT Y T ps OT f,
    (Project.FirstOrderSemantics.reduct M).mem rT (v 4) ∧ CompositionGraph (v 0) pi r rT ∧
    Data R Hdom env v G F mul g q bound labels E r Ar Hr X Q pr O ∧
    Data R Hdom env v G F mul gT q bound labels E rT AT HT Y T ps OT ∧
    Injection Q T f ∧ ForcingLocalQuotientTransport.Graph (v 6) a pr ps f ∧
    Injection O OT b ∧ Restricts b f O ∧
    ∀ y, (Project.FirstOrderSemantics.reduct M).mem y OT →
      ∃ x, (Project.FirstOrderSemantics.reduct M).mem x O ∧ PureKuratowski.PairMember M x y b

theorem row_unique (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    {R : Formula (k+2)} {Hdom : Formula (k+1)} {env : Fin k → M.Carrier .set} {v : Fin 7 → M.Carrier .set}
    {I G F mul g gT q bound labels E pi a r b d : M.Carrier .set}
    (hDiagrams : ForcingDiagramCarrier.Carrier (v 0) I (v 4))
    (hb : Row R Hdom env v G F mul g gT q bound labels E pi a r b)
    (hd : Row R Hdom env v G F mul g gT q bound labels E pi a r d) : b = d := by
  obtain ⟨rT,Ar,Hr,X,Q,pr,O,AT,HT,Y,T,ps,OT,f,hrT,hComp,hD,hDT,hf,hGraph,hb,hB,_⟩ := hb
  obtain ⟨rT',Ar',Hr',X',Q',pr',O',AT',HT',Y',T',ps',OT',f',hrT',hComp',hD',hDT',hf',hGraph',hd,hDres,_⟩ := hd
  have hRT := ForcingDiagramAction.unique hM ((hDiagrams rT).mp hrT) ((hDiagrams rT').mp hrT') hComp hComp'
  subst rT'
  obtain ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩ := ForcingEligibleFamily.data_unique hM hD hD'
  obtain ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩ := ForcingEligibleFamily.data_unique hM hDT hDT'
  have hff : f = f' := SetTheory.Structure.IsSetRelation.eq_of_pairMember_iff (ModelTransfer.extensionality hM)
    ((ForcingSupportSize.native_mapsTo hM _ _ f).mp hf.1).1.1
    ((ForcingSupportSize.native_mapsTo hM _ _ f').mp hf'.1).1.1
    (fun x y => (hGraph x y).trans (hGraph' x y).symm)
  subst f'
  exact SetTheory.Structure.IsSetRelation.eq_of_pairMember_iff (ModelTransfer.extensionality hM)
    ((ForcingSupportSize.native_mapsTo hM _ _ b).mp hb.1).1.1
    ((ForcingSupportSize.native_mapsTo hM _ _ d).mp hd.1).1.1
    (fun x y => (hB x y).trans (hDres x y).symm)

theorem exists_row (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (G F mul a : Fin k)
    {I K B w e mu pi inv c ai ac g gT q A Hq labelMap top bit labels E bound r : M.Carrier .set}
    (hm : ForcingDiagramPoset.LeftCancelMonoid (env (rho 0)) (env mul) e)
    (hData : ForcingProductCovariance.SystemData (fun j => env (rho j)) I K B w (env G) (env F) mu pi inv c (env a) ai)
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) (hSmall : ForcingSupportSize.Small w mu)
    (hNormal : ForcingNormalFilter.Normal I (env G) (env F)) (hLabelMap : ForcingConditionGraphs.FunctionOn K labelMap)
    (hTop : ForcingWithTopCarrier.Empty top) (hLabels : ForcingLabelSet.LabelSet (env (rho 6)) I K labelMap top bit labels)
    (hBound : ForcingPowerName.Bound (env (rho 6)) labels bound)
    (hc : ForcingLocalTransport.CohenPart (env (rho 1)) (env (rho 2)) (env (rho 3)) pi ac)
    (hg : ForcingLocalAtomic.CohenFilter (env (rho 3)) g) (hImage : ForcingStabilizerTransport.Image ac g gT)
    (hq : Injection (env (rho 0)) I q) (hA : ForcingSupportedNames.Range (env (rho 0)) q A)
    (hHq : ForcingLabelPermutations.Fixing (env G) A Hq) (hpiHq : (Project.FirstOrderSemantics.reduct M).mem pi Hq)
    (hE : ForcingSupportedNames.Supported (fun j => env (rho j)) Hq E)
    (hr : (Project.FirstOrderSemantics.reduct M).mem r (env (rho 4))) :
    ∃ b, Row (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) env (fun j => env (rho j))
      (env G) (env F) (env mul) g gT q bound labels E pi (env a) r b := by
  have hDiagrams := hData.1.2.2.2.1
  have hrI := (hDiagrams r).mp hr
  obtain ⟨rT,hrT,hComp⟩ := ForcingDiagramAction.exists_permute hM hData.2.2.1 hrI
  obtain ⟨O,Ar,Hr,X,Q,pr,hSource⟩ := ForcingEligibleFamily.exists_row hM (orderFormula (rho 0) mul)
    (ForcingPairUnion.domain rho G F) env (fun j => env (rho j)) (env G) (env F) (env mul) g q bound labels E hrI
  obtain ⟨OT,AT,HT,Y,T,ps,hTarget⟩ := ForcingEligibleFamily.exists_row hM (orderFormula (rho 0) mul)
    (ForcingPairUnion.domain rho G F) env (fun j => env (rho j)) (env G) (env F) (env mul) gT q bound labels E hrT
  obtain ⟨f,b,hf,hGraph,hb,hRes,hOnto⟩ := ForcingEligibleTransport.assemble_app hM env rho G F mul a hm hData hw hSmall hNormal
    hLabelMap hTop hLabels hBound hc hg hImage hrI hrT hComp hq hA hHq hpiHq hE hSource hTarget
  exact ⟨b,rT,Ar,Hr,X,Q,pr,O,AT,HT,Y,T,ps,OT,f,(hDiagrams rT).mpr hrT,hComp,hSource,hTarget,hf,hGraph,hb,hRes,hOnto⟩

def row {k m : Nat} (R : Formula (k+2)) (Hdom : Formula (k+1)) (base : Fin k → Fin m) (rho : Fin 7 → Fin m)
    (G F mul g gT q bound labels E pi a r b : Fin m) : Formula m :=
  let up := fun j : Fin m => j.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc
  let rr := fun j => up (rho j)
  let bb := fun j => up (base j)
  let rT := (Fin.last m).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc
  let Ar := (Fin.last (m+1)).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc
  let Hr := (Fin.last (m+2)).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc
  let X := (Fin.last (m+3)).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc
  let Q := (Fin.last (m+4)).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc
  let pr := (Fin.last (m+5)).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc
  let O := (Fin.last (m+6)).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc
  let AT := (Fin.last (m+7)).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc
  let HT := (Fin.last (m+8)).castSucc.castSucc.castSucc.castSucc.castSucc
  let Y := (Fin.last (m+9)).castSucc.castSucc.castSucc.castSucc
  let T := (Fin.last (m+10)).castSucc.castSucc.castSucc
  let ps := (Fin.last (m+11)).castSucc.castSucc
  let OT := (Fin.last (m+12)).castSucc
  let f := (Fin.last (m+13))
  let body := ((Formula.mem rT (rr 4)).conj
    ((ForcingConditionGraphs.compositionGraph (rr 0) (up pi) (up r) rT).conj
    ((ForcingEligibleFamily.data R Hdom bb rr (up G) (up F) (up mul) (up g) (up q) (up bound) (up labels) (up E) (up r) Ar Hr X Q pr O).conj
    ((ForcingEligibleFamily.data R Hdom bb rr (up G) (up F) (up mul) (up gT) (up q) (up bound) (up labels) (up E) rT AT HT Y T ps OT).conj
    ((Source.SetLanguage.injection f Q T).conj
    ((ForcingLocalQuotientTransport.graph (rr 6) (up a) pr ps f).conj
    ((Source.SetLanguage.injection (up b) O OT).conj
    ((RestrictionSyntax.edgeLaw (up b) f O).conj
    (ForcingEligibleTransport.onto (up b) O OT)))))))))
  .ex (.ex (.ex (.ex (.ex (.ex (.ex (.ex (.ex (.ex (.ex (.ex (.ex (.ex (body))))))))))))))

theorem row_semantics {k m : Nat} (env : Fin m → M.Carrier .set) (R : Formula (k+2)) (Hdom : Formula (k+1))
    (base : Fin k → Fin m) (rho : Fin 7 → Fin m) (G F mul g gT q bound labels E pi a r b : Fin m) :
    Formula.Realize (Project.FirstOrderSemantics.reduct M).mem env (row R Hdom base rho G F mul g gT q bound labels E pi a r b) ↔
      Row R Hdom (fun j => env (base j)) (fun j => env (rho j)) (env G) (env F) (env mul) (env g) (env gT) (env q) (env bound) (env labels) (env E) (env pi) (env a) (env r) (env b) := by
  simp only [row,Row,Formula.Realize,ForcingConditionGraphs.compositionGraph_semantics (M := M),
    ForcingEligibleFamily.data_semantics (M := M),ForcingSupportSize.injection_semantics (M := M),
    ForcingLocalQuotientTransport.graph_semantics (M := M),ForcingEligibleRestriction.edgeLaw_semantics (M := M),
    ForcingEligibleTransport.onto_semantics (M := M),Fin.lastCases_last,Fin.lastCases_castSucc]
  rfl

def Family {k : Nat} (R : Formula (k+2)) (Hdom : Formula (k+1))
    (env : Fin k → M.Carrier .set) (v : Fin 7 → M.Carrier .set)
    (G F mul g gT q bound labels E pi a apps : M.Carrier .set) : Prop :=
  ∀ r b, PureKuratowski.PairMember M r b apps ↔
    (Project.FirstOrderSemantics.reduct M).mem r (v 4) ∧ Row R Hdom env v G F mul g gT q bound labels E pi a r b

def family {k m : Nat} (R : Formula (k+2)) (Hdom : Formula (k+1)) (base : Fin k → Fin m) (rho : Fin 7 → Fin m)
    (G F mul g gT q bound labels E pi a apps : Fin m) : Formula m :=
  let up := fun j : Fin m => j.castSucc.castSucc
  .all (.all ((Source.SetLanguage.edge (up apps) (Fin.last m).castSucc (Fin.last (m+1))).iff
    ((Formula.mem (Fin.last m).castSucc (up (rho 4))).conj
      (row R Hdom (fun j => up (base j)) (fun j => up (rho j))
        (up G) (up F) (up mul) (up g) (up gT) (up q) (up bound) (up labels) (up E) (up pi) (up a) (Fin.last m).castSucc (Fin.last (m+1))))))

theorem family_semantics {k m : Nat} (env : Fin m → M.Carrier .set) (R : Formula (k+2)) (Hdom : Formula (k+1))
    (base : Fin k → Fin m) (rho : Fin 7 → Fin m) (G F mul g gT q bound labels E pi a apps : Fin m) :
    Formula.Realize (Project.FirstOrderSemantics.reduct M).mem env (family R Hdom base rho G F mul g gT q bound labels E pi a apps) ↔
      Family R Hdom (fun j => env (base j)) (fun j => env (rho j))
        (env G) (env F) (env mul) (env g) (env gT) (env q) (env bound) (env labels) (env E) (env pi) (env a) (env apps) := by
  simp only [family,Family,Source.Formula.iff,Formula.Realize,KuratowskiZF.source_edge,
    row_semantics (M := M),Fin.lastCases_last,Fin.lastCases_castSucc]
  exact ⟨fun h r b => ⟨(h r b).1,(h r b).2⟩,fun h r b => ⟨(h r b).mp,(h r b).mpr⟩⟩

theorem exists_family (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (R : Formula (k+2)) (Hdom : Formula (k+1)) (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k)
    (G F mul g gT q bound labels E pi a : Fin k) {I : M.Carrier .set}
    (hDiagrams : ForcingDiagramCarrier.Carrier (env (rho 0)) I (env (rho 4)))
    (hTotal : ∀ r, (Project.FirstOrderSemantics.reduct M).mem r (env (rho 4)) →
      ∃ b, Row R Hdom env (fun j => env (rho j)) (env G) (env F) (env mul) (env g) (env gT)
        (env q) (env bound) (env labels) (env E) (env pi) (env a) r b) :
    ∃ image apps, MapsTo (env (rho 4)) image apps ∧ Family R Hdom env (fun j => env (rho j))
      (env G) (env F) (env mul) (env g) (env gT) (env q) (env bound) (env labels) (env E) (env pi) (env a) apps := by
  let up := fun j : Fin k => j.castSucc.castSucc
  let query := row R Hdom up (fun j => up (rho j)) (up G) (up F) (up mul) (up g) (up gT) (up q)
    (up bound) (up labels) (up E) (up pi) (up a) (Fin.last k).castSucc (Fin.last (k+1))
  let penv : SetTheory.Env (Project.FirstOrderSemantics.reduct M) k :=
    { bound := fun j => env j.rev, free := fun _ => env (rho 4) }
  have he r b : (ProjectSyntax.binary query).denote penv r b ↔
      Row R Hdom env (fun j => env (rho j)) (env G) (env F) (env mul) (env g) (env gT)
        (env q) (env bound) (env labels) (env E) (env pi) (env a) r b := by
    rw [ForcingMapConditions.binary_semantics hM query env (env (rho 4)) r b]
    simp only [ForcingMapConditions.MapRel,query,row_semantics (M := M),up,Fin.lastCases_last,Fin.lastCases_castSucc]
  have ht : ∀ r, (Project.FirstOrderSemantics.reduct M).mem r (env (rho 4)) →
      ∃ b, (ProjectSyntax.binary query).denote penv r b := by
    intro r hr
    obtain ⟨b,hb⟩ := hTotal r hr
    exact ⟨b,(he r b).mpr hb⟩
  have hu : ∀ r b d, (ProjectSyntax.binary query).denote penv r b → (ProjectSyntax.binary query).denote penv r d → b = d :=
    fun r b d hb hd => row_unique hM hDiagrams ((he r b).mp hb) ((he r d).mp hd)
  obtain ⟨image,hImage⟩ := ZF.exists_functionalImage (ModelTransfer.project_models_iff.mp hM) (ProjectSyntax.binary query) penv (env (rho 4)) ht hu
  obtain ⟨apps,hApps,hEdge⟩ := ZF.exists_setFunctionFromTo_of_denote (ModelTransfer.project_models_iff.mp hM)
    (KuratowskiZF.interpretation hM) (ProjectSyntax.binary query) penv ht (fun r _ b d hb hd => hu r b d hb hd)
    (fun r b hr hb => (hImage b).mpr ⟨r,hr,hb⟩)
  exact ⟨image,apps,(ForcingSupportSize.native_mapsTo hM _ _ _).mpr hApps,
    fun r b => (hEdge r b).trans (and_congr Iff.rfl (he r b))⟩


theorem app_data (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    {R : Formula (k+2)} {Hdom : Formula (k+1)} {env : Fin k → M.Carrier .set} {v : Fin 7 → M.Carrier .set}
    {I G F mul g gT q bound labels E pi a objects targets apps r rT O OT b : M.Carrier .set}
    (hDiagrams : ForcingDiagramCarrier.Carrier (v 0) I (v 4))
    (hObj : ForcingEligibleFamily.Family R Hdom env v G F mul g q bound labels E (v 4) objects)
    (hTarget : ForcingEligibleFamily.Family R Hdom env v G F mul gT q bound labels E (v 4) targets)
    (hFamily : Family R Hdom env v G F mul g gT q bound labels E pi a apps)
    (hComp : CompositionGraph (v 0) pi r rT) (hr : PureKuratowski.PairMember M r O objects)
    (hT : PureKuratowski.PairMember M rT OT targets) (hb : PureKuratowski.PairMember M r b apps) :
    ∃ Ar Hr X Q pr AT HT Y T ps f,
      Data R Hdom env v G F mul g q bound labels E r Ar Hr X Q pr O ∧
      Data R Hdom env v G F mul gT q bound labels E rT AT HT Y T ps OT ∧
      Injection Q T f ∧ ForcingLocalQuotientTransport.Graph (v 6) a pr ps f ∧
      Injection O OT b ∧ Restricts b f O ∧
      ∀ y, (Project.FirstOrderSemantics.reduct M).mem y OT →
        ∃ x, (Project.FirstOrderSemantics.reduct M).mem x O ∧ PureKuratowski.PairMember M x y b := by
  obtain ⟨rT',Ar,Hr,X,Q,pr,O',AT,HT,Y,T,ps,OT',f,hrT',hComp',hD,hDT,hf,hGraph,hb,hRes,hOnto⟩ := ((hFamily r b).mp hb).2
  have he := ForcingDiagramAction.unique hM ((hDiagrams rT).mp ((hTarget rT OT).mp hT).1)
    ((hDiagrams rT').mp hrT') hComp hComp'
  subst rT'
  have ho := ForcingEligibleFamily.row_unique hM ((hObj r O).mp hr).2 ⟨Ar,Hr,X,Q,pr,hD⟩
  have ht := ForcingEligibleFamily.row_unique hM ((hTarget rT OT).mp hT).2 ⟨AT,HT,Y,T,ps,hDT⟩
  subst O'; subst OT'
  exact ⟨Ar,Hr,X,Q,pr,AT,HT,Y,T,ps,f,hD,hDT,hf,hGraph,hb,hRes,hOnto⟩

theorem apps_of_family (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    {R : Formula (k+2)} {Hdom : Formula (k+1)} {env : Fin k → M.Carrier .set} {v : Fin 7 → M.Carrier .set}
    {I G F mul g gT q bound labels E pi a objects targets image apps : M.Carrier .set}
    (hDiagrams : ForcingDiagramCarrier.Carrier (v 0) I (v 4))
    (hObj : ForcingEligibleFamily.Family R Hdom env v G F mul g q bound labels E (v 4) objects)
    (hTarget : ForcingEligibleFamily.Family R Hdom env v G F mul gT q bound labels E (v 4) targets)
    (hMap : MapsTo (v 4) image apps)
    (hFamily : Family R Hdom env v G F mul g gT q bound labels E pi a apps) :
    ForcingReindexSystem.Apps (v 0) pi objects targets apps := by
  intro r rT O OT hComp hr hT
  obtain ⟨b,hb,_⟩ := hMap.1.2 r ((hObj r O).mp hr).1
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,hInj,_,hOnto⟩ := app_data hM hDiagrams hObj hTarget hFamily hComp hr hT hb
  exact ⟨b,hb,hInj,hOnto⟩

theorem natural_of_family (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    {R : Formula (k+2)} {Hdom : Formula (k+1)} {env : Fin k → M.Carrier .set} {v : Fin 7 → M.Carrier .set}
    {I G F mul g gT q bound labels E pi act objects targets objImage targetImage arrows maps targetMaps apps : M.Carrier .set}
    (hDiagrams : ForcingDiagramCarrier.Carrier (v 0) I (v 4))
    (hObjMap : MapsTo (v 4) objImage objects) (hTargetMap : MapsTo (v 4) targetImage targets)
    (hObj : ForcingEligibleFamily.Family R Hdom env v G F mul g q bound labels E (v 4) objects)
    (hTarget : ForcingEligibleFamily.Family R Hdom env v G F mul gT q bound labels E (v 4) targets)
    (hArrows : ForcingEligibleMapFamily.Arrows (v 0) mul (v 4) arrows)
    (hMaps : ForcingEligibleMapFamily.Family R Hdom env v G F mul g q bound labels E arrows maps)
    (hTargetMaps : ForcingEligibleMapFamily.Family R Hdom env v G F mul gT q bound labels E arrows targetMaps)
    (hFamily : Family R Hdom env v G F mul g gT q bound labels E pi act apps) :
    ForcingReindexSystem.Natural (v 0) pi maps targetMaps apps := by
  intro r s rT sT z zT f g' a b x y xT yT hCompR hCompS hz hzT hf hg ha hb hxy hxxT hyyT
  obtain ⟨s',r',hs,hr,_,hz'⟩ := (hArrows z).mp ((hMaps z f).mp hf).1
  obtain ⟨rfl,rfl⟩ := PureKuratowski.code_injective hz hz'
  obtain ⟨sT',rT',hsT,hrT,_,hzT'⟩ := (hArrows zT).mp ((hTargetMaps zT g').mp hg).1
  obtain ⟨rfl,rfl⟩ := PureKuratowski.code_injective hzT hzT'
  obtain ⟨Os,hos,_⟩ := hObjMap.1.2 s hs
  obtain ⟨Or,hor,_⟩ := hObjMap.1.2 r hr
  obtain ⟨OTs,hots,_⟩ := hTargetMap.1.2 sT hsT
  obtain ⟨OTr,hotr,_⟩ := hTargetMap.1.2 rT hrT
  obtain ⟨As,Hs,Xs,Qs,ps,Ar,Hr,Xr,Qr,pr,f0,hDs,hDr,hf0,hF,_,hFres⟩ := ForcingEligibleSystem.map_data hM hObj hMaps hos hor hz hf
  obtain ⟨ATs,HTs,Ys,Ts,pts,ATr,HTr,Yr,Tr,ptr,g0,hDTs,hDTr,hg0,hG,_,hGres⟩ := ForcingEligibleSystem.map_data hM hTarget hTargetMaps hots hotr hzT hg
  obtain ⟨As',Hs',Xs',Qs',ps',ATs',HTs',Ys',Ts',pts',bs,hDs',hDTs',hbs,hBs,hbInj,hBres,_⟩ := app_data hM hDiagrams hObj hTarget hFamily hCompS hos hots hb
  obtain ⟨rfl,rfl,rfl,rfl,rfl,_⟩ := ForcingEligibleFamily.data_unique hM hDs hDs'
  obtain ⟨rfl,rfl,rfl,rfl,rfl,_⟩ := ForcingEligibleFamily.data_unique hM hDTs hDTs'
  obtain ⟨Ar',Hr',Xr',Qr',pr',ATr',HTr',Yr',Tr',ptr',ar,hDr',hDTr',har,hAr,_,hAres,_⟩ := app_data hM hDiagrams hObj hTarget hFamily hCompR hor hotr ha
  obtain ⟨rfl,rfl,rfl,rfl,rfl,_⟩ := ForcingEligibleFamily.data_unique hM hDr hDr'
  obtain ⟨rfl,rfl,rfl,rfl,rfl,_⟩ := ForcingEligibleFamily.data_unique hM hDTr hDTr'
  have hLe := ForcingEligibleSystem.map_order hArrows hMaps hz hf
  have hLeT := ForcingEligibleSystem.map_order hArrows hTargetMaps hzT hg
  have hSub : ForcingPowerName.Subset As Ar := fun t ht =>
    (hDr.1 t).mpr (ConstructionDescentPlacement.range_antitone hLe ((hDs.1 t).mp ht))
  have hSubT : ForcingPowerName.Subset ATs ATr := fun t ht =>
    (hDTr.1 t).mpr (ConstructionDescentPlacement.range_antitone hLeT ((hDTs.1 t).mp ht))
  have hNames := ForcingLocalNames.restrict_name hDs.2.1 hDr.2.1 hSub hDs.2.2.1 hDr.2.2.1
  have hNamesT := ForcingLocalNames.restrict_name hDTs.2.1 hDTr.2.1 hSubT hDTs.2.2.1 hDTr.2.2.1
  obtain ⟨sigma,tau,hpx,hAct,hptx⟩ := (hBs x xT).mp ((hBres x xT).mp hxxT).1
  obtain ⟨y',hpy,_⟩ := hDr.2.2.2.1.1.2 sigma (hNames sigma (ForcingConditionGraphs.function_input hDs.2.2.2.1.1 hpx))
  have hyy := ForcingConditionGraphs.function_unique hf0.1 (ForcingLocalRestriction.restrict_ofName hF hpx hpy) ((hFres x y).mp hxy).1
  subst y'
  obtain ⟨yT',hpty,_⟩ := hDTr.2.2.2.1.1.2 tau (hNamesT tau (ForcingConditionGraphs.function_input hDTs.2.2.2.1.1 hptx))
  have he := ForcingConditionGraphs.function_unique har.1.1 ((hAr y yT').mpr ⟨sigma,tau,hpy,hAct,hpty⟩) ((hAres y yT).mp hyyT).1
  subst yT'
  exact (hGres xT yT).mpr ⟨ForcingLocalRestriction.restrict_ofName hG hptx hpty,hbInj.1.2 x xT hxxT⟩


def constructionSentence {k : Nat} (rho : Fin 7 → Fin k) (G F mul a I K B w e mu pi inv c ai ac g gT q A Hq labelMap top bit labels E bound objImage objects targetImage targets arrows maps targetMaps : Fin k) : Project.Sentence where
  formula := Project.Formula.forallClosure k
    (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid (rho 0) mul e))
      (.imp (ProjectSyntax.encode id (ForcingProductCovariance.systemData rho I K B w G F mu pi inv c a ai))
      (.imp (Project.Formula.isOmega (.bound w))
      (.imp (ProjectSyntax.encode id (ForcingSupportSize.small w mu))
      (.imp (ProjectSyntax.encode id (ForcingNormalFilter.normal I G F))
      (.imp (ProjectSyntax.encode id (Source.SetLanguage.functionOn labelMap K))
      (.imp (ProjectSyntax.encode id (ForcingWithTopCarrier.empty top))
      (.imp (ProjectSyntax.encode id (ForcingLabelSet.labelSet (rho 6) I K labelMap top bit labels))
      (.imp (ProjectSyntax.encode id (ForcingLabelBound.bound (rho 6) labels bound))
      (.imp (ProjectSyntax.encode id (ForcingLocalTransport.cohenPart (rho 1) (rho 2) (rho 3) pi ac))
      (.imp (ProjectSyntax.encode id (ForcingLocalAtomic.cohenFilter (rho 3) g))
      (.imp (ProjectSyntax.encode id (ForcingStabilizerTransport.image ac g gT))
      (.imp (ProjectSyntax.encode id (Source.SetLanguage.injection q (rho 0) I))
      (.imp (ProjectSyntax.encode id (ForcingSupportedNames.range (rho 0) q A))
      (.imp (ProjectSyntax.encode id (ForcingLabelPermutations.fixing G A Hq))
      (.imp (ProjectSyntax.encode id (Formula.mem pi Hq))
      (.imp (ProjectSyntax.encode id (ForcingEquivariantMix.fixedAll rho Hq E))
      (.imp (ProjectSyntax.encode id (Source.SetLanguage.mapsTo objects (rho 4) objImage))
      (.imp (ProjectSyntax.encode id (Source.SetLanguage.mapsTo targets (rho 4) targetImage))
      (.imp (ProjectSyntax.encode id (ForcingEligibleFamily.family (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) id rho G F mul g q bound labels E (rho 4) objects))
      (.imp (ProjectSyntax.encode id (ForcingEligibleFamily.family (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) id rho G F mul gT q bound labels E (rho 4) targets))
      (.imp (ProjectSyntax.encode id (ForcingEligibleMapFamily.arrows (rho 0) mul (rho 4) arrows))
      (.imp (ProjectSyntax.encode id (ForcingEligibleMapFamily.family (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) id rho G F mul g q bound labels E arrows maps))
      (.imp (ProjectSyntax.encode id (ForcingEligibleMapFamily.family (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) id rho G F mul gT q bound labels E arrows targetMaps))
      (.existsE (.existsE (.conj (ProjectSyntax.encode id (Source.SetLanguage.mapsTo 0 (rho 4).succ.succ 1)) (.conj (ProjectSyntax.encode id (family (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) (fun j => j.succ.succ) (fun j => (rho j).succ.succ) G.succ.succ F.succ.succ mul.succ.succ g.succ.succ gT.succ.succ q.succ.succ bound.succ.succ labels.succ.succ E.succ.succ pi.succ.succ a.succ.succ 0)) (.conj (ForcingReindexSystem.appsF (rho 0).succ.succ pi.succ.succ objects.succ.succ targets.succ.succ 0) (ForcingReindexSystem.natural (rho 0).succ.succ pi.succ.succ maps.succ.succ targetMaps.succ.succ 0))))))))))))))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,Project.Formula.isOmega,ProjectSyntax.freeClosed,
      ForcingReindexSystem.appsF_freeClosed,ForcingReindexSystem.natural_freeClosed]

theorem construction_models {k : Nat} (rho : Fin 7 → Fin k) (G F mul a I K B w e mu pi inv c ai ac g gT q A Hq labelMap top bit labels E bound objImage objects targetImage targets arrows maps targetMaps : Fin k)
    (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (constructionSentence rho G F mul a I K B w e mu pi inv c ai ac g gT q A Hq labelMap top bit labels E bound objImage objects targetImage targets arrows maps targetMaps)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) (constructionSentence rho G F mul a I K B w e mu pi inv c ai ac g gT q A Hq labelMap top bit labels E bound objImage objects targetImage targets arrows maps targetMaps)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro env
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_isOmega_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),ForcingProductCovariance.systemData_semantics (M := M),
    ForcingSupportSize.small_semantics (M := M),ForcingNormalFilter.normal_semantics (M := M),
    ForcingConditionGraphs.functionOn_semantics (M := M),ForcingWithTopCarrier.empty_semantics (M := M),
    ForcingLabelSet.labelSet_semantics (M := M),ForcingLabelBound.bound_semantics (M := M),
    ForcingLocalTransport.cohenPart_semantics (M := M),ForcingLocalAtomic.cohenFilter_semantics (M := M),
    ForcingStabilizerTransport.image_semantics (M := M),ForcingSupportSize.injection_semantics (M := M),
    ForcingSupportedNames.range_semantics (M := M),ForcingLabelPermutations.fixing_semantics (M := M),
    Formula.Realize,ForcingSupportedNames.supported_semantics (M := M),ForcingSupportSize.mapsTo_semantics (M := M),
    ForcingEligibleFamily.family_semantics (M := M),ForcingEligibleMapFamily.arrows_semantics (M := M),
    ForcingEligibleMapFamily.family_semantics (M := M),family_semantics (M := M),
    ForcingReindexSystem.appsF_semantics hM,ForcingReindexSystem.natural_semantics hM]
  intro hm hData hw hSmall hNormal hLabelMap hTop hLabels hBound hc hg hImage hq hA hHq hpiHq hE
    hObjMap hTargetMap hObj hTarget hArrows hMaps hTargetMaps
  obtain ⟨image,apps,hAppMap,hFamily⟩ := exists_family hM (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) env rho
    G F mul g gT q bound labels E pi a hData.1.2.2.2.1
    (fun r hr => exists_row hM env rho G F mul a hm hData hw hSmall hNormal hLabelMap hTop hLabels hBound hc hg hImage hq hA hHq hpiHq hE hr)
  exact ⟨image,apps,hAppMap,hFamily,
    apps_of_family hM hData.1.2.2.2.1 hObj hTarget hAppMap hFamily,
    natural_of_family hM hData.1.2.2.2.1 hObjMap hTargetMap hObj hTarget hArrows hMaps hTargetMaps hFamily⟩

theorem construction_kernel_certificate {k : Nat} (rho : Fin 7 → Fin k) (G F mul a I K B w e mu pi inv c ai ac g gT q A Hq labelMap top bit labels E bound objImage objects targetImage targets arrows maps targetMaps : Fin k) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (constructionSentence rho G F mul a I K B w e mu pi inv c ai ac g gT q A Hq labelMap top bit labels E bound objImage objects targetImage targets arrows maps targetMaps)) :=
  ModelTransfer.derives (fun _ hM => construction_models rho G F mul a I K B w e mu pi inv c ai ac g gT q A Hq labelMap top bit labels E bound objImage objects targetImage targets arrows maps targetMaps hM)

end PPAC.Migration.ForcingEligibleReindex
