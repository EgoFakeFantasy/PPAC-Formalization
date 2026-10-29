/- Pinned GraphFusion.ForcedAvailable/mem_forcedAvailability:512-566 and
PersistentCodes.eligibleSystem_availability_eq/exists_fiber_principal:326-363.
Use actual normalized names and the existing quotient/restriction family. -/
import PPAC.Migration.ForcingWorksCovariance

namespace PPAC.Migration.ForcingForcedAvailability
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open Source (Formula)
open ForcingProductSymmetry (orderFormula)
open ForcingPrincipalFilter (EqF)
open ForcingSupportSize (MapsTo Injection)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 6000000
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def Available {k : Nat} (R : Formula (k+2)) (env : Fin k → M.Carrier .set)
    (v : Fin 7 → M.Carrier .set) (G F mul bound d r tau n : M.Carrier .set) : Prop :=
  ∃ s A H sigma, (Project.FirstOrderSemantics.reduct M).mem s (v 4) ∧
    ForcingDiagramOrder.Sub (v 0) mul r n s ∧ ForcingSupportedNames.Range (v 0) s A ∧
    ForcingLabelPermutations.Fixing G A H ∧ ForcingLocalNames.LocalName v G F bound H sigma ∧
    EqF R env (v 6) d r sigma tau

def available {k m : Nat} (R : Formula (k+2)) (base : Fin k → Fin m)
    (rho : Fin 7 → Fin m) (G F mul bound d r tau n : Fin m) : Project.Formula 1 m :=
  let up : Fin m → Fin (m+4) := fun i => i.succ.succ.succ.succ
  .existsE (.existsE (.existsE (.existsE
    (.conj (.mem (.bound 3) (.bound (up (rho 4))))
    (.conj (ProjectSyntax.encode id (ForcingDiagramOrder.sub (up (rho 0)) (up mul) (up r) (up n) 3))
    (.conj (ProjectSyntax.encode id (ForcingSupportedNames.range (up (rho 0)) 3 2))
    (.conj (ProjectSyntax.encode id (ForcingLabelPermutations.fixing (up G) 2 1))
    (.conj (ProjectSyntax.encode id (ForcingLocalNames.localName (fun j => up (rho j)) (up G) (up F) (up bound) 1 0))
      (ForcingPrincipalFilter.eqF R (fun j => up (base j)) (up (rho 6)) (up d) (up r) 0 (up tau))))))))))

theorem available_freeClosed {k m : Nat} (R : Formula (k+2)) (base : Fin k → Fin m)
    (rho : Fin 7 → Fin m) (G F mul bound d r tau n : Fin m) :
    (available R base rho G F mul bound d r tau n).FreeClosed := by
  simp -implicitDefEqProofs [available,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,ForcingPrincipalFilter.eqF_freeClosed]

theorem available_semantics (hM : FirstOrder.Theory.Models M nativeZF) {k m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (R : Formula (k+2)) (base : Fin k → Fin m)
    (rho : Fin 7 → Fin m) (G F mul bound d r tau n : Fin m) :
    Project.Formula.satisfies env (available R base rho G F mul bound d r tau n) ↔
      Available R (fun j => env.bound (base j)) (fun j => env.bound (rho j)) (env.bound G) (env.bound F)
        (env.bound mul) (env.bound bound) (env.bound d) (env.bound r) (env.bound tau) (env.bound n) := by
  simp only [available,Available,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingDiagramOrder.sub_semantics (M := M),ForcingSupportedNames.range_semantics (M := M),
    ForcingLabelPermutations.fixing_semantics (M := M),ForcingLocalNames.localName_semantics (M := M),
    ForcingPrincipalFilter.eqF_semantics hM]
  rfl

theorem actual_available_iff (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (G F mul : Fin k)
    {w mu history kappa one mark H C incoming base I K B labelMap top bit labels bound E q Aq Hq
      d g oi objects S mi maps r a Ar Hr X Q pr Or tau x n : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hMu : (Project.FirstOrderSemantics.reduct M).IsInfiniteCardinal (KuratowskiZF.interpretation hM) w mu)
    (hI : (Project.FirstOrderSemantics.reduct M).IsHartogsNumber (KuratowskiZF.interpretation hM) I mu)
    (hSmall : ForcingSupportSize.Small (env (rho 0)) mu)
    (hMergers : ConstructionSaturationMergers.AllMergers w history kappa)
    (hRow : ConstructionTowerHistory.Row history kappa (env (rho 0)) (env mul) one mark H C incoming base kappa)
    (hm : ForcingDiagramPoset.LeftCancelMonoid (env (rho 0)) (env mul) one)
    (hp : ForcingProductFamily.Presentation (env (rho 0)) I K B w (env (rho 1)) (env (rho 2))
      (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hG : ForcingLabelPermutations.Carrier I (env G)) (hF : ForcingSupportFilter.Filter I (env G) mu (env F))
    (hLabelMap : ForcingConditionGraphs.FunctionOn K labelMap) (hTop : ForcingWithTopCarrier.Empty top)
    (hLabels : ForcingLabelSet.LabelSet (env (rho 6)) I K labelMap top bit labels)
    (hq : Injection (env (rho 0)) I q) (hAq : ForcingSupportedNames.Range (env (rho 0)) q Aq)
    (hHq : ForcingLabelPermutations.Fixing (env G) Aq Hq)
    (hE : ForcingSupportedNames.Supported (fun j => env (rho j)) Hq E)
    (hd : (Project.FirstOrderSemantics.reduct M).mem d (env (rho 3)))
    (hg : ForcingPrincipalFilter.Principal (env (rho 3)) d g)
    (hObjMap : MapsTo (env (rho 4)) oi objects)
    (hObj : ForcingEligibleFamily.Family (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) env
      (fun j => env (rho j)) (env G) (env F) (env mul) g q bound labels E (env (rho 4)) objects)
    (hS : ForcingEligibleMapFamily.Arrows (env (rho 0)) (env mul) (env (rho 4)) S)
    (hMap : MapsTo S mi maps)
    (hMaps : ForcingEligibleMapFamily.Family (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) env
      (fun j => env (rho j)) (env G) (env F) (env mul) g q bound labels E S maps)
    (hSys : ForcingEligibleSystem.System (env (rho 0)) objects maps)
    (hr : PureKuratowski.PairMember M r Or objects)
    (hDr : ForcingEligibleFamily.Data (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) env
      (fun j => env (rho j)) (env G) (env F) (env mul) g q bound labels E r Ar Hr X Q pr Or)
    (hRoot : ForcingDiagramOrder.Sub (env (rho 0)) (env mul) r a q)
    (hTau : PureKuratowski.PairMember M tau x pr)
    (hx : (Project.FirstOrderSemantics.reduct M).mem x Or)
    (hn : (Project.FirstOrderSemantics.reduct M).mem n (env (rho 0)))
    (hna : ConstructionBaseMonoid.Divides (env (rho 0)) (env mul) n a) :
    ForcingSystemAvailability.Available (env (rho 0)) (env mul) objects maps r x n ↔
      Available (orderFormula (rho 0) mul) env (fun j => env (rho j)) (env G) (env F) (env mul) bound d r tau n := by
  have hrI := (hp.2.2.2.1 r).mp (ForcingConditionGraphs.function_input hObjMap.1 hr)
  have hgf := ForcingPrincipalFilter.principal_filter hd hg
  constructor
  · rintro ⟨s,Os,z,f,y,hSub,hs,hz,hf,hy,hyx⟩
    obtain ⟨As,Hs,Xs,Qs,ps,Ar',Hr',X',Q',pr',fQ,hDs,hDr',_,hRestr,_,hRes⟩ :=
      ForcingEligibleSystem.map_data hM hObj hMaps hs hr hz hf
    obtain ⟨rfl,rfl,rfl,rfl,rfl,_⟩ := ForcingEligibleFamily.data_unique hM hDr hDr'
    obtain ⟨sigma,hsy,hsx⟩ := (hRestr y x).mp ((hRes y x).mp hyx).1
    have he := (ForcingLocalQuotient.equality_law hM env rho mul hm hp hgf hrI hDr.2.2.2.2.2.1 sigma tau x x hsx hTau).mp rfl
    exact ⟨s,As,Hs,sigma,ForcingConditionGraphs.function_input hObjMap.1 hs,hSub,hDs.1,hDs.2.1,
      (hDs.2.2.1 sigma).mp ((hDs.2.2.2.2.2.1 sigma y).mp hsy).1,
      (ForcingPrincipalFilter.eqG_principal hM env rho mul hm hp hd hrI hg).mp he⟩
  · rintro ⟨s,As,Hs,sigma,hsD,hSub,hAs,hHs,hSigma,he⟩
    have hsI := (hp.2.2.2.1 s).mp hsD
    obtain ⟨Os,hs,_⟩ := hObjMap.1.2 s hsD
    obtain ⟨z,f,hz,hf,_⟩ := ForcingSystemAvailability.exists_map hM hObjMap hS hMap hSys hr hs ⟨n,hn,hSub⟩
    obtain ⟨As',Hs',Xs,Qs,ps,Ar',Hr',X',Q',pr',fQ,hDs,hDr',_,hRestr,_,hRes⟩ :=
      ForcingEligibleSystem.map_data hM hObj hMaps hs hr hz hf
    obtain ⟨rfl,rfl,rfl,rfl,rfl,_⟩ := ForcingEligibleFamily.data_unique hM hDr hDr'
    have eAs := (ModelTransfer.extensionality hM).eq_of_same_members As As' (fun z => (hAs z).trans (hDs.1 z).symm)
    subst As'
    have eHs := ForcingLabelPermutations.fixing_unique hM hHs hDs.2.1
    subst Hs'
    have hsigmaXs := (hDs.2.2.1 sigma).mpr hSigma
    have hRange : ForcingPowerName.Subset As Ar := fun z hz => (hDr.1 z).mpr
      (ConstructionDescentPlacement.range_antitone ⟨n,hn,hSub⟩ ((hAs z).mp hz))
    have hsigmaX := ForcingLocalNames.restrict_name hHs hDr.2.1 hRange hDs.2.2.1 hDr.2.2.1 sigma hsigmaXs
    obtain ⟨y,hsy,_⟩ := hDs.2.2.2.1.1.2 sigma hsigmaXs
    obtain ⟨x',hsx',_⟩ := hDr.2.2.2.1.1.2 sigma hsigmaX
    have ex : x' = x := (ForcingLocalQuotient.equality_law hM env rho mul hm hp hgf hrI hDr.2.2.2.2.2.1 sigma tau x' x hsx' hTau).mpr
      ((ForcingPrincipalFilter.eqG_principal hM env rho mul hm hp hd hrI hg).mpr he)
    subst x'
    have hyx := ForcingLocalRestriction.restrict_ofName hRestr hsy hsx'
    have hsq := ForcingSystemAvailability.sub_mono hM hm hsI hq hn hna hSub hRoot
    have hAqs : ForcingPowerName.Subset Aq As := fun z hz => (hAs z).mpr
      (ConstructionDescentPlacement.range_antitone hsq ((hAq z).mp hz))
    have hEs := ForcingSupportedNames.supported_mono hHq hHs hAqs hE
    have hEligible := (ForcingEligibilityReflection.eligible_restrict_iff hM hChoice env rho G F mul
      hw hMu hI hSmall hMergers hRow hm hp hG hF hsI hrI ⟨n,hn,hSub⟩ hAs hHs hgf
      hLabelMap hTop hLabels hEs hDs.2.2.1 hDs.2.2.2.2.2.1 hDr.2.2.2.2.2.1 hRestr hyx).mp
        ((hDr.2.2.2.2.2.2 x).mp hx).2.2
    have hy : (Project.FirstOrderSemantics.reduct M).mem y Os :=
      (hDs.2.2.2.2.2.2 y).mpr ⟨hDs.2.2.2.1.2 sigma y hsy,hsq,hEligible⟩
    exact ⟨s,Os,z,f,y,hSub,hs,hz,hf,hy,(hRes y x).mpr ⟨hyx,hy⟩⟩

def Carrier {k : Nat} (R : Formula (k+2)) (env : Fin k → M.Carrier .set)
    (v : Fin 7 → M.Carrier .set) (G F mul bound d r a tau U : M.Carrier .set) : Prop :=
  ∀ n, (Project.FirstOrderSemantics.reduct M).mem n U ↔
    (Project.FirstOrderSemantics.reduct M).mem n (v 0) ∧ ConstructionBaseMonoid.Divides (v 0) mul n a ∧
      Available R env v G F mul bound d r tau n

def carrier {k m : Nat} (R : Formula (k+2)) (base : Fin k → Fin m) (rho : Fin 7 → Fin m)
    (G F mul bound d r a tau U : Fin m) : Project.Formula 1 m :=
  .forallE (.iff (.mem (.bound 0) (.bound U.succ))
    (.conj (.mem (.bound 0) (.bound (rho 0).succ))
    (.conj (ProjectSyntax.encode id (ConstructionBaseMonoid.divides (rho 0).succ mul.succ 0 a.succ))
      (available R (fun j => (base j).succ) (fun j => (rho j).succ)
        G.succ F.succ mul.succ bound.succ d.succ r.succ tau.succ 0))))

theorem carrier_freeClosed {k m : Nat} (R : Formula (k+2)) (base : Fin k → Fin m) (rho : Fin 7 → Fin m)
    (G F mul bound d r a tau U : Fin m) : (carrier R base rho G F mul bound d r a tau U).FreeClosed := by
  simp -implicitDefEqProofs [carrier,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,available_freeClosed]

theorem carrier_semantics (hM : FirstOrder.Theory.Models M nativeZF) {k m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (R : Formula (k+2)) (base : Fin k → Fin m)
    (rho : Fin 7 → Fin m) (G F mul bound d r a tau U : Fin m) :
    Project.Formula.satisfies env (carrier R base rho G F mul bound d r a tau U) ↔
      Carrier R (fun j => env.bound (base j)) (fun j => env.bound (rho j)) (env.bound G) (env.bound F)
        (env.bound mul) (env.bound bound) (env.bound d) (env.bound r) (env.bound a) (env.bound tau) (env.bound U) := by
  simp only [carrier,Carrier,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_iff_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,Project.Formula.satisfies_conj_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ConstructionBaseMonoid.divides_semantics (M := M),
    available_semantics hM]
  rfl

theorem exists_carrier (hM : FirstOrder.Theory.Models M nativeZF) {k m : Nat}
    (R : Formula (k+2)) (env : Fin m → M.Carrier .set) (base : Fin k → Fin m) (rho : Fin 7 → Fin m)
    (G F mul bound d r a tau : Fin m) :
    ∃ U, Carrier R (fun j => env (base j)) (fun j => env (rho j)) (env G) (env F) (env mul)
      (env bound) (env d) (env r) (env a) (env tau) U := by
  let schema : Project.UnarySchema m := {
    body := .conj (ProjectSyntax.encode id (ConstructionBaseMonoid.divides (rho 0).succ mul.succ 0 a.succ))
      (available R (fun j => (base j).succ) (fun j => (rho j).succ) G.succ F.succ mul.succ bound.succ d.succ r.succ tau.succ 0)
    freeClosed := by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,available_freeClosed] }
  let penv : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m := {bound := env,free := fun _ => env (rho 0)}
  obtain ⟨U,hU⟩ := ZF.separation_exists_d (ModelTransfer.project_models_iff.mp hM) schema penv (env (rho 0))
  refine ⟨U,fun n => ?_⟩
  simpa only [schema,penv,Project.UnarySchema.denote,Project.Formula.satisfies_conj_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ConstructionBaseMonoid.divides_semantics (M := M),
    available_semantics hM] using! hU n

/-- The chosen normalized name has a class in the actual exact fiber.
System laws are obtained from the existing family producer, not assumed. -/
theorem exists_fiber_principal (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (G F mul : Fin k)
    {w mu history kappa one mark H C incoming base I K B labelMap top bit labels bound E q Aq Hq
      d g oi objects S mi maps r a Ar Hr X Q pr Or tau U z : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hMu : (Project.FirstOrderSemantics.reduct M).IsInfiniteCardinal (KuratowskiZF.interpretation hM) w mu)
    (hI : (Project.FirstOrderSemantics.reduct M).IsHartogsNumber (KuratowskiZF.interpretation hM) I mu)
    (hSmall : ForcingSupportSize.Small (env (rho 0)) mu)
    (hMergers : ConstructionSaturationMergers.AllMergers w history kappa)
    (hRow : ConstructionTowerHistory.Row history kappa (env (rho 0)) (env mul) one mark H C incoming base kappa)
    (hm : ForcingDiagramPoset.LeftCancelMonoid (env (rho 0)) (env mul) one)
    (hp : ForcingProductFamily.Presentation (env (rho 0)) I K B w (env (rho 1)) (env (rho 2))
      (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hG : ForcingLabelPermutations.Carrier I (env G)) (hF : ForcingSupportFilter.Filter I (env G) mu (env F))
    (hLabelMap : ForcingConditionGraphs.FunctionOn K labelMap) (hTop : ForcingWithTopCarrier.Empty top)
    (hLabels : ForcingLabelSet.LabelSet (env (rho 6)) I K labelMap top bit labels)
    (hq : Injection (env (rho 0)) I q) (hAq : ForcingSupportedNames.Range (env (rho 0)) q Aq)
    (hHq : ForcingLabelPermutations.Fixing (env G) Aq Hq)
    (hE : ForcingSupportedNames.Supported (fun j => env (rho j)) Hq E)
    (hd : (Project.FirstOrderSemantics.reduct M).mem d (env (rho 3)))
    (hg : ForcingPrincipalFilter.Principal (env (rho 3)) d g)
    (hObjMap : MapsTo (env (rho 4)) oi objects)
    (hObj : ForcingEligibleFamily.Family (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) env
      (fun j => env (rho j)) (env G) (env F) (env mul) g q bound labels E (env (rho 4)) objects)
    (hS : ForcingEligibleMapFamily.Arrows (env (rho 0)) (env mul) (env (rho 4)) S)
    (hMap : MapsTo S mi maps)
    (hMaps : ForcingEligibleMapFamily.Family (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) env
      (fun j => env (rho j)) (env G) (env F) (env mul) g q bound labels E S maps)
    (hr : PureKuratowski.PairMember M r Or objects)
    (hDr : ForcingEligibleFamily.Data (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) env
      (fun j => env (rho j)) (env G) (env F) (env mul) g q bound labels E r Ar Hr X Q pr Or)
    (hRoot : ForcingDiagramOrder.Sub (env (rho 0)) (env mul) r a q)
    (hLabelBound : ForcingLabelBound.LabelBound (env (rho 6)) I K labelMap top bit bound)
    (ha : (Project.FirstOrderSemantics.reduct M).mem a (env (rho 0)))
    (hTau : (Project.FirstOrderSemantics.reduct M).mem tau X)
    (hz : ForcingSupportingRoot.Code z d r)
    (hForce : ForcingFormula.Force (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) env
      (Source.SetLanguage.args3 tau labels E) (env (rho 6)) z (ForcingEligibility.isClass 0 1 2))
    (hU : Carrier (orderFormula (rho 0) mul) env (fun j => env (rho j)) (env G) (env F) (env mul) bound d r a tau U) :
    ∃ x fiber, PureKuratowski.PairMember M tau x pr ∧
      ForcingSystemFibers.Fiber (env (rho 0)) (env mul) objects maps r Or a U fiber ∧
      (Project.FirstOrderSemantics.reduct M).mem x fiber := by
  have hgf := ForcingPrincipalFilter.principal_filter hd hg
  have hSys := ForcingEligibleSystem.system_of_families hM hChoice env rho G F mul
    hw hMu hI hSmall hMergers hRow hm hp hG hF hLabelMap hTop hLabels hLabelBound
    hgf hq hAq hHq hE hObj hS hMaps
  obtain ⟨x,htx,_⟩ := hDr.2.2.2.1.1.2 tau hTau
  have hx : (Project.FirstOrderSemantics.reduct M).mem x Or := (hDr.2.2.2.2.2.2 x).mpr
    ⟨hDr.2.2.2.1.2 tau x htx,⟨a,ha,hRoot⟩,tau,htx,d,z,(hg d).mpr ⟨hd,fun _ h => h⟩,hz,hForce⟩
  have hActual : ForcingSystemAvailability.Carrier (env (rho 0)) (env mul) objects maps r x a U := by
    intro n
    rw [hU n]
    apply and_congr_right
    intro hn
    apply and_congr_right
    intro hna
    exact (actual_available_iff hM hChoice env rho G F mul hw hMu hI hSmall hMergers hRow hm hp hG hF
      hLabelMap hTop hLabels hq hAq hHq hE hd hg hObjMap hObj hS hMap hMaps hSys hr hDr hRoot htx hx hn hna).symm
  obtain ⟨fiber,hFiber⟩ := ForcingSystemFibers.exists_fiber hM (env (rho 0)) (env mul) objects maps r Or a U
  exact ⟨x,fiber,htx,hFiber,(hFiber x).mpr ⟨hx,hActual⟩⟩

def carrierSentence {k m : Nat} (R : Formula (k+2)) (base : Fin k → Fin m) (rho : Fin 7 → Fin m)
    (G F mul bound d r a tau : Fin m) : Project.Sentence where
  formula := Project.Formula.forallClosure m (.existsE
    (carrier R (fun j => (base j).succ) (fun j => (rho j).succ)
      G.succ F.succ mul.succ bound.succ d.succ r.succ a.succ tau.succ 0))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,carrier_freeClosed]

theorem carrier_models {k m : Nat} (R : Formula (k+2)) (base : Fin k → Fin m) (rho : Fin 7 → Fin m)
    (G F mul bound d r a tau : Fin m) (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (carrierSentence R base rho G F mul bound d r a tau)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM),SetTheory.Structure.satisfiesSentence_iff]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro env
  simp only [Project.Formula.satisfies_exists_iff,carrier_semantics hM]
  exact exists_carrier hM R env base rho G F mul bound d r a tau

theorem carrier_kernel_certificate {k m : Nat} (R : Formula (k+2)) (base : Fin k → Fin m) (rho : Fin 7 → Fin m)
    (G F mul bound d r a tau : Fin m) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (carrierSentence R base rho G F mul bound d r a tau)) :=
  ModelTransfer.derives (fun _ hM => carrier_models R base rho G F mul bound d r a tau hM)

/-- Pinned principal-fiber bridge, with the actual object and restriction families. -/
def fiberSentence {k : Nat} (rho : Fin 7 → Fin k) (w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq d g oi objects S mi maps r a Ar Hr X Q pr Or tau U z : Fin k) : Project.Sentence where
  formula :=
    let up : Fin k → Fin (k+2) := fun j => j.succ.succ
    Project.Formula.forallClosure k
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
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.functionOn labelMap K))
    (.imp (ProjectSyntax.encode id (ForcingWithTopCarrier.empty top))
    (.imp (ProjectSyntax.encode id (ForcingLabelSet.labelSet (rho 6) I K labelMap top bit labels))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.injection q (rho 0) I))
    (.imp (ProjectSyntax.encode id (ForcingSupportedNames.range (rho 0) q Aq))
    (.imp (ProjectSyntax.encode id (ForcingLabelPermutations.fixing G Aq Hq))
    (.imp (ProjectSyntax.encode id (ForcingEquivariantMix.fixedAll rho Hq E))
    (.imp (.mem (.bound d) (.bound (rho 3)))
    (.imp (ForcingPrincipalFilter.principal (rho 3) d g)
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.mapsTo objects (rho 4) oi))
    (.imp (ProjectSyntax.encode id (ForcingEligibleFamily.family (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) id rho G F mul g q bound labels E (rho 4) objects))
    (.imp (ProjectSyntax.encode id (ForcingEligibleMapFamily.arrows (rho 0) mul (rho 4) S))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.mapsTo maps S mi))
    (.imp (ProjectSyntax.encode id (ForcingEligibleMapFamily.family (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) id rho G F mul g q bound labels E S maps))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge objects r Or))
    (.imp (ProjectSyntax.encode id (ForcingEligibleFamily.data (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) id rho G F mul g q bound labels E r Ar Hr X Q pr Or))
    (.imp (ProjectSyntax.encode id (ForcingDiagramOrder.sub (rho 0) mul r a q))
    (.imp (ProjectSyntax.encode id (ForcingLabelBound.labelBound (rho 6) I K labelMap top bit bound))
    (.imp (.mem (.bound a) (.bound (rho 0)))
    (.imp (.mem (.bound tau) (.bound X))
    (.imp (ProjectSyntax.encode id (ForcingSupportingRoot.code z d r))
    (.imp (ProjectSyntax.encode id (ForcingFormula.formula (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) id (Source.SetLanguage.args3 tau labels E) (rho 6) z (ForcingEligibility.isClass 0 1 2)))
    (.imp (carrier (orderFormula (rho 0) mul) id rho G F mul bound d r a tau U)
    (.existsE (.existsE (.conj
      (ProjectSyntax.encode id (Source.SetLanguage.edge (up pr) (up tau) 1))
      (.conj (ProjectSyntax.encode id (ForcingSystemFibers.fiber (up (rho 0)) (up mul) (up objects) (up maps) (up r) (up Or) (up a) (up U) 0))
        (.mem (.bound 1) (.bound 0)))))))))))))))))))))))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
      ConstructionSaturationIndex.hartogs_freeClosed,ConstructionSaturationMergers.allMergers_freeClosed,
      ConstructionTowerHistory.row_freeClosed,carrier_freeClosed,ForcingPrincipalFilter.principal_freeClosed]

theorem fiber_models {k : Nat} (rho : Fin 7 → Fin k) (w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq d g oi objects S mi maps r a Ar Hr X Q pr Or tau U z : Fin k)
    (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) :
    (Project.fo_sentence (fiberSentence rho w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq d g oi objects S mi maps r a Ar Hr X Q pr Or tau U z)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM),SetTheory.Structure.satisfiesSentence_iff]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro env
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    Project.Formula.satisfies_isOmega_iff,
    Project.Formula.satisfies_isInfiniteCardinal_iff (KuratowskiZF.interpretation hM) (ModelTransfer.extensionality hM),
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ConstructionSaturationIndex.hartogs_semantics hM,ForcingSupportSize.small_semantics (M := M),
    ConstructionSaturationMergers.allMergers_semantics hM,ConstructionTowerHistory.row_semantics hM,
    ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),ForcingProductFamily.presentation_semantics (M := M),
    ForcingLabelPermutations.carrier_semantics (M := M),ForcingSupportFilter.filter_semantics (M := M),
    ForcingConditionGraphs.functionOn_semantics (M := M),ForcingWithTopCarrier.empty_semantics (M := M),
    ForcingLabelSet.labelSet_semantics (M := M),ForcingSupportSize.injection_semantics (M := M),
    ForcingSupportedNames.range_semantics (M := M),ForcingLabelPermutations.fixing_semantics (M := M),
    ForcingSupportedNames.supported_semantics (M := M),ForcingPrincipalFilter.principal_semantics (M := M),
    ForcingSupportSize.mapsTo_semantics (M := M),ForcingEligibleFamily.family_semantics (M := M),
    ForcingEligibleMapFamily.arrows_semantics (M := M),ForcingEligibleMapFamily.family_semantics (M := M),
    KuratowskiZF.source_edge,ForcingEligibleFamily.data_semantics (M := M),ForcingDiagramOrder.sub_semantics (M := M),
    ForcingLabelBound.labelBound_semantics (M := M),ForcingSupportingRoot.code_semantics (M := M),
    ForcingFormula.formula_semantics (M := M),carrier_semantics hM,ForcingSystemFibers.fiber_semantics (M := M)]
  exact exists_fiber_principal hM hChoice env rho G F mul

theorem fiber_kernel_certificate {k : Nat} (rho : Fin 7 → Fin k) (w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq d g oi objects S mi maps r a Ar Hr X Q pr Or tau U z : Fin k) :
    FirstOrder.Derives nativeZF []
      (Project.fo_sentence (ConstructibleGround.relative (fiberSentence rho w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq d g oi objects S mi maps r a Ar Hr X Q pr Or tau U z))) := by
  apply ModelTransfer.derives
  intro M hM
  have hL := ConstructibleSource.model_zf hM
  have hRawChoice := (Project.FirstOrderSemantics.sentence_correct
    (ModelTransfer.extensionality hL) Axioms.choice).mp (ConstructibleSource.model_choice hM)
  let witness := Classical.choice ((ConstructibleSource.model hM).nonempty .set)
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct (ConstructibleSource.model hM)) 0 :=
    { bound := Fin.elim0, free := fun _ => witness }
  have hSat : Project.Formula.satisfies env (ConstructionDirectedCardinality.choice (m := 0)) := by
    change Project.Formula.satisfies env (Axioms.choice.formula.rename Fin.elim0)
    rw [Project.Formula.satisfies_rename]
    exact hRawChoice env.free
  have hChoice := (ConstructionDirectedCardinality.choice_semantics hL env).mp hSat
  apply ConstructibleGround.relative_models hM (fiberSentence rho w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq d g oi objects S mi maps r a Ar Hr X Q pr Or tau U z)
  exact (Project.FirstOrderSemantics.sentence_correct
    (ModelTransfer.extensionality hL) (fiberSentence rho w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq d g oi objects S mi maps r a Ar Hr X Q pr Or tau U z)).mp
      (fiber_models rho w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq d g oi objects S mi maps r a Ar Hr X Q pr Or tau U z hL hChoice)

end PPAC.Migration.ForcingForcedAvailability
