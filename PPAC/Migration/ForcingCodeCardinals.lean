/- Fixed CodeCardinals.ordinalType_cardinal_le:45-116.
Use one literal internal record relation for totality and compatible single-valuedness.
Names, ranks, diagrams and pulled-back conditions are the existing source constructions. -/
import PPAC.Migration.ForcingCodeRecordWitness
import PPAC.Migration.ForcingRelationClassMove
import PPAC.Migration.ForcingCohenChainBound

namespace PPAC.Migration.ForcingCodeCardinals
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open Source (Formula)
open ForcingProductSymmetry (orderFormula)
open ForcingSupportSize (Injection)
open ConstructionComponentCarrier (Code)
open ConstructionComponentCofinal (Chain)
open ForcingTailCodes (Entry)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 3000000
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def Record {k : Nat} (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k)
    (w I K G F mul labelMap top bit labels bound E q root chain r localS codes order ranks : Fin k) (p rec beta : M.Carrier .set) : Prop :=
  ∃ a rankName nb zr tau s m x j name z pb inner,
      (Project.FirstOrderSemantics.reduct M).mem a (env codes) ∧
      PureKuratowski.PairMember M a rankName (env ranks) ∧
      ForcingCheckName.Checked (env top) beta nb ∧
      ForcingSupportingRoot.Code zr p (env r) ∧
      ForcingAtomicRelations.Forces true (orderFormula (rho 0) mul) env (env (rho 6)) rankName nb zr ∧
      ForcingCohenConditions.Condition (env (rho 2)) (env w) p  ∧
      ForcingCodeSelection.IsSelected env rho I G F mul q bound labels E root w chain codes order a p ∧
      Entry (fun j => env (rho j)) (env G) (env F) (env bound) (env root) tau ∧
      ForcingCodeLinks.Links (orderFormula (rho 0) mul) env (env (rho 6)) (env w) (env (rho 0)) (env I) (env mul) (env q) (env chain) p (env root) tau a ∧
      Injection (env (rho 0)) (env I) s ∧
      (Project.FirstOrderSemantics.reduct M).mem m (env (rho 0)) ∧ ForcingDiagramOrder.Sub (env (rho 0)) (env mul) s m (env r) ∧
      (Project.FirstOrderSemantics.reduct M).mem x (env (rho 0)) ∧ PureKuratowski.PairMember M x j s ∧
      ForcingMapConditions.MapRel (ForcingRelationClassMove.family rho G F mul I K labelMap top bit labels E) env j name ∧
      ForcingSupportingRoot.Code z p s ∧ ForcingAtomicRelations.Forces true (orderFormula (rho 0) mul) env (env (rho 6)) tau name z ∧
      ForcingLocalRecordPullback.Supported (env (rho 0)) s p ∧
      ForcingCohenConditions.Condition (env localS) (env w) pb ∧ ForcingLocalRecordPullback.Pullback (env (rho 0)) s p pb ∧
      PureKuratowski.Code M inner x pb ∧ PureKuratowski.Code M rec m inner


def record {k n : Nat} (rho : Fin 7 → Fin k) (w I K G F mul labelMap top bit labels bound E q root chain r localS codes order ranks : Fin k)
    (base : Fin k → Fin n) (p rec beta : Fin n) : Project.Formula 1 n :=
  let L := orderFormula (rho 0) mul
  let up : Fin n → Fin (n+13) := fun j => j.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  let body : Project.Formula 1 (n+13) :=
    (.conj (.mem (.bound 12) (.bound (up (base codes))))
    (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge (up (base ranks)) 12 11))
    (.conj (ProjectSyntax.encode id (ForcingCheckName.checkName (up (base top)) (up beta) 10))
    (.conj (ProjectSyntax.encode id (ForcingSupportingRoot.code 9 (up p) (up (base r))))
    (.conj (ProjectSyntax.encode id (ForcingAtomicRelations.forces true L (fun i => up (base i)) (up (base (rho 6))) 11 10 9))
    (.conj (ProjectSyntax.encode id (ForcingCohenConditions.condition (up (base (rho 2))) (up (base w)) (up p)))
    (.conj (ForcingCodeSelection.selected rho I G F mul q bound labels E root w chain codes order (fun i => up (base i)) 12 (up p))
    (.conj (ForcingTailCodes.entry (fun i => up (base (rho i))) (up (base G)) (up (base F)) (up (base bound)) (up (base root)) 8)
    (.conj (ForcingCodeLinks.links L (fun i => up (base i)) (up (base (rho 6))) (up (base w)) (up (base (rho 0))) (up (base I)) (up (base mul)) (up (base q)) (up (base chain)) (up p) (up (base root)) 8 12)
    (.conj (ProjectSyntax.encode id (Source.SetLanguage.injection 7 (up (base (rho 0))) (up (base I))))
    (.conj (.mem (.bound 6) (.bound (up (base (rho 0)))))
    (.conj (ProjectSyntax.encode id (ForcingDiagramOrder.sub (up (base (rho 0))) (up (base mul)) 7 6 (up (base r))))
    (.conj (.mem (.bound 5) (.bound (up (base (rho 0)))))
    (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge 7 5 4))
    (.conj (ProjectSyntax.encode id (ReplacementPredicates.rel (ForcingRelationClassMove.family rho G F mul I K labelMap top bit labels E) (fun i => up (base i)) 4 3))
    (.conj (ProjectSyntax.encode id (ForcingSupportingRoot.code 2 (up p) 7))
    (.conj (ProjectSyntax.encode id (ForcingAtomicRelations.forces true L (fun i => up (base i)) (up (base (rho 6))) 8 3 2))
    (.conj (ForcingLocalRecordPullback.supported (up (base (rho 0))) 7 (up p))
    (.conj (ProjectSyntax.encode id (ForcingCohenConditions.condition (up (base localS)) (up (base w)) 1))
    (.conj (ForcingLocalRecordPullback.pullback (up (base (rho 0))) 7 (up p) 1)
    (.conj (ProjectSyntax.encode id (PairSyntax.ordered 0 5 1))
    (ProjectSyntax.encode id (PairSyntax.ordered (up rec) 6 0)))))))))))))))))))))))
  .existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (body)))))))))))))

theorem record_freeClosed {k n : Nat} (rho : Fin 7 → Fin k) (w I K G F mul labelMap top bit labels bound E q root chain r localS codes order ranks : Fin k)
    (base : Fin k → Fin n) (p rec beta : Fin n) : (record rho w I K G F mul labelMap top bit labels bound E q root chain r localS codes order ranks base p rec beta).FreeClosed := by
  simp -implicitDefEqProofs [record,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
    ForcingCodeSelection.selected_freeClosed,ForcingTailCodes.entry_freeClosed,ForcingCodeLinks.links_freeClosed,
    ForcingLocalRecordPullback.supported_freeClosed,ForcingLocalRecordPullback.pullback_freeClosed]

theorem record_semantics (hM : FirstOrder.Theory.Models M nativeZF) {k n : Nat}
    (rho : Fin 7 → Fin k) (w I K G F mul labelMap top bit labels bound E q root chain r localS codes order ranks : Fin k) (base : Fin k → Fin n) (p rec beta : Fin n)
    (env : Env (Project.FirstOrderSemantics.reduct M) n) :
    Project.Formula.satisfies env (record rho w I K G F mul labelMap top bit labels bound E q root chain r localS codes order ranks base p rec beta) ↔
      Record (fun i => env.bound (base i)) rho w I K G F mul labelMap top bit labels bound E q root chain r localS codes order ranks (env.bound p) (env.bound rec) (env.bound beta) := by
  simp only [record,Record,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    KuratowskiZF.source_edge,ForcingSupportingRoot.code_semantics (M := M),ForcingAtomicRelations.forces_semantics (M := M),
    ForcingCheckName.checkName_semantics (M := M),ForcingCohenConditions.condition_semantics (M := M),
    ForcingCodeSelection.selected_semantics hM,ForcingTailCodes.entry_semantics hM,ForcingCodeLinks.links_semantics hM,
    ForcingSupportSize.injection_semantics (M := M),ForcingDiagramOrder.sub_semantics (M := M),
    ForcingMapConditions.rel_semantics (M := M),ForcingLocalRecordPullback.supported_semantics hM,
    ForcingLocalRecordPullback.pullback_semantics hM,KuratowskiZF.source_code]
  rfl

private theorem entry_supported (hM : FirstOrder.Theory.Models M nativeZF)
    {v : Fin 7 → M.Carrier .set} {G F bound root r index U A fixing tau : M.Carrier .set}
    (hRoot : Code root r index U) (hRange : ForcingSupportedNames.Range (v 0) r A)
    (hFix : ForcingLabelPermutations.Fixing G A fixing) (hEntry : Entry v G F bound root tau) :
    ForcingSupportedNames.Supported v fixing tau := by
  obtain ⟨r',i',U',A',fixing',hc,hA',hFix',hName⟩ := hEntry
  obtain ⟨rfl,rfl,rfl⟩ := ConstructionComponentCarrier.code_injective hRoot hc
  have hAA := (ModelTransfer.extensionality hM).eq_of_same_members A A' (fun x => (hRange x).trans (hA' x).symm)
  subst A'
  have hFF := ForcingLabelPermutations.fixing_unique hM hFix hFix'
  subst fixing'
  exact hName.2

theorem single (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k)
    (w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq zero root vertices chain names r index U Ar Hr localS codes order ranks : Fin k) {d0 d1 rec beta gamma : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega (env w))
    (hMu : (Project.FirstOrderSemantics.reduct M).IsInfiniteCardinal (KuratowskiZF.interpretation hM) (env w) (env mu))
    (hI : (Project.FirstOrderSemantics.reduct M).IsHartogsNumber (KuratowskiZF.interpretation hM) (env I) (env mu))
    (hSmall : ForcingSupportSize.Small (env (rho 0)) (env mu))
    (hMergers : ConstructionSaturationMergers.AllMergers (env w) (env history) (env kappa))
    (hRow : ConstructionTowerHistory.Row (env history) (env kappa) (env (rho 0)) (env mul) (env one) (env mark) (env H) (env C) (env incoming) (env base) (env kappa))
    (hm : ForcingDiagramPoset.LeftCancelMonoid (env (rho 0)) (env mul) (env one))

    (hp : ForcingProductFamily.Presentation (env (rho 0)) (env I) (env K) (env B) (env w) (env (rho 1)) (env (rho 2))
      (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hG : ForcingLabelPermutations.Carrier (env I) (env G)) (hF : ForcingSupportFilter.Filter (env I) (env G) (env mu) (env F))
    (hLabelMap : ForcingConditionGraphs.FunctionOn (env K) (env labelMap))
    (hTop : ForcingWithTopCarrier.Empty (env top))
    (hLabels : ForcingLabelSet.LabelSet (env (rho 6)) (env I) (env K) (env labelMap) (env top) (env bit) (env labels))


    (hAq : ForcingSupportedNames.Range (env (rho 0)) (env q) (env Aq))
    (hHq : ForcingLabelPermutations.Fixing (env G) (env Aq) (env Hq))
    (hE : ForcingSupportedNames.Supported (fun j => env (rho j)) (env Hq) (env E))

    (hChain : Chain (env w) (env (rho 0)) (env I) (env mul) (env q) (env zero) (env root) (env vertices) (env chain))

    (hRoot : Code (env root) (env r) (env index) (env U))
    (hCodes : ForcingTailCodes.Carrier (fun j => env (rho j)) (env G) (env F) (env bound) (env w) (env names) (env chain) (env codes))
    (hRange : ForcingSupportedNames.Range (env (rho 0)) (env r) (env Ar))
    (hFix : ForcingLabelPermutations.Fixing (env G) (env Ar) (env Hr))
    (hWO : (Project.FirstOrderSemantics.reduct M).IsSetCodedWellOrder (KuratowskiZF.interpretation hM) (env order) (env codes))
    (hRanks : ForcingConditionGraphs.FunctionOn (env codes) (env ranks))
    (h0 : Record env rho w I K G F mul labelMap top bit labels bound E q root chain r localS codes order ranks d0 rec beta) (h1 : Record env rho w I K G F mul labelMap top bit labels bound E q root chain r localS codes order ranks d1 rec gamma)
    (hcompat : ConstructionCohenCompatibility.Compatible d0 d1) : beta = gamma := by
  obtain ⟨a,rankName,nb,zr,tau,s,m,x,j,name,z,pb,inner,ha,han,hnb,hzr,hRank,hd0,hsa,hEntry,hLinks,hs,hmD,hSub,hx,hxj,hFamily,hz,hForce,hSupport,hpb,hPullback,hInner,hRec⟩ := h0
  obtain ⟨a',rankName',ng,zr',tau',s',m',x',j',name',z',pb',inner',ha',han',hng,hzr',hRank',hd1,hsb,hEntry',hLinks',hs',hmD',hSub',hx',hxj',hFamily',hz',hForce',hSupport',hpb',hPullback',hInner',hRec'⟩ := h1
  obtain ⟨rfl,rfl⟩ := PureKuratowski.code_injective hRec hRec'
  obtain ⟨rfl,rfl⟩ := PureKuratowski.code_injective hInner hInner'
  have hCommon := hChain.2.2.2.1 (env zero) (env root) hChain.2.1
  obtain ⟨r',i',U',t',b',V',hc,_,hv,_,_⟩ := hCommon
  obtain ⟨rfl,rfl,rfl⟩ := ConstructionComponentCarrier.code_injective hRoot hc
  have hEf := ForcingSupportedNames.supported_mono hHq hFix
    (fun y hy => (hRange y).mpr (ConstructionDescentPlacement.range_antitone
      ⟨env index,hv.2.2.2.1,hv.2.1⟩ ((hAq y).mp hy))) hE
  have hCov := ForcingRelationClassMove.covariance hM env rho G F mul I K labelMap top bit labels E
    hp hG hF hw hMu hLabelMap hTop hLabels hFix hEf
  obtain ⟨dR,zR,hRestricted,hdR,hzR,hEq⟩ := ForcingLocalRecordEquality.equal_at_root hM hChoice
    (ForcingRelationClassMove.family rho G F mul I K labelMap top bit labels E) env rho G F mul
    hw hMu hI hSmall hMergers hRow hm hp hG hF hv.1 hs hs' hmD hSub hSub' hxj hxj'
    hRange hFix (entry_supported hM hRoot hRange hFix hEntry) (entry_supported hM hRoot hRange hFix hEntry')
    hCov hFamily hFamily' hd0 hd1 hSupport hSupport' hPullback hPullback' hz hz' hForce hForce'
  obtain ⟨f,hf,_,h0f,h1f⟩ := ConstructionCohenCompatibility.exists_union hM hw hd0 hd1 hcompat
  have hfP := (hp.2.2.1 f).mpr hf
  have hRF : ForcingPowerName.Subset dR f := fun y hy => h1f y ((hRestricted y).mp hy).1
  have hEqF := ForcingPrincipalFilter.eqF_mono hM env rho mul hm hp hfP hv.1 hRF ⟨zR,hzR,hEq⟩
  have hSame := (ForcingCodeLinks.links_eq_iff_same hM hChoice env rho G F mul
    hw hMu hI hSmall hMergers hRow hm hp hG hF hChain hfP hRoot ((hCodes a).mp ha) ((hCodes a').mp ha')
    (ForcingCodeLinks.links_mono hM env rho mul hm hp hfP h0f hLinks)
    (ForcingCodeLinks.links_mono hM env rho mul hm hp hfP h1f hLinks')).mp hEqF
  have haa := ForcingPersistentSelection.selected_unique hM
    (E := ForcingPersistentCodes.Same (orderFormula (rho 0) mul) env (env (rho 6)) (env w) (env chain)) hWO
    (fun _ _ _ _ _ _ h => ForcingPersistentCodes.same_symm hM h) hfP (fun _ h => h) ha ha'
    (ForcingCodeSelection.isSelected_mono h0f hsa) (ForcingCodeSelection.isSelected_mono h1f hsb) hSame
  subst a'
  have hn := ForcingConditionGraphs.function_unique hRanks han han'
  subst rankName'
  have he0 := ForcingPrincipalFilter.eqF_mono hM env rho mul hm hp hfP hv.1 h0f ⟨zr,hzr,hRank⟩
  have he1 := ForcingPrincipalFilter.eqF_mono hM env rho mul hm hp hfP hv.1 h1f ⟨zr',hzr',hRank'⟩
  obtain ⟨zf,hzf,hcheck⟩ := ForcingPrincipalFilter.eqF_trans hM env rho mul hm hp hfP hv.1
    (ForcingPrincipalFilter.eqF_symm hM he0) he1
  have hpre := ForcingProductPoset.preorder env (rho 0) mul (rho 6) hm hp.2.2.2.2.1 hp.2.2.2.1 hp.2.2.2.2.2
  have htopW := (hp.2.2.2.2.2 (env top)).mpr (Or.inl hTop)
  have htop : ∀ v, (Project.FirstOrderSemantics.reduct M).mem v (env (rho 6)) →
      ForcingMapConditions.MapRel (orderFormula (rho 0) mul) env v (env top) :=
    fun v _ => (ForcingProductSymmetry.orderFormula_semantics env (rho 0) mul v (env top)).mpr (Or.inl hTop)
  exact (ForcingCheckReflection.eq_check_iff hM hpre htopW htop
    (ForcingSupportingRoot.code_mem hp hf hv.1 hzf) hnb hng).mp hcheck

theorem total (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k)
    (w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq zero root vertices chain names r index U coordS localS codes order Ar Hr support ranks selection d z0 theta ntheta : Fin k)
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega (env w))
    (hMu : (Project.FirstOrderSemantics.reduct M).IsInfiniteCardinal (KuratowskiZF.interpretation hM) (env w) (env mu))
    (hI : (Project.FirstOrderSemantics.reduct M).IsHartogsNumber (KuratowskiZF.interpretation hM) (env I) (env mu))
    (hSmall : ForcingSupportSize.Small (env (rho 0)) (env mu))
    (hMergers : ConstructionSaturationMergers.AllMergers (env w) (env history) (env kappa))
    (hRow : ConstructionTowerHistory.Row (env history) (env kappa) (env (rho 0)) (env mul) (env one) (env mark) (env H) (env C) (env incoming) (env base) (env kappa))
    (hm : ForcingDiagramPoset.LeftCancelMonoid (env (rho 0)) (env mul) (env one))
    (hJ : ConstructionProbeSharedIntersections.ConditionalJoins (env (rho 0)) (env mul))
    (hp : ForcingProductFamily.Presentation (env (rho 0)) (env I) (env K) (env B) (env w) (env (rho 1)) (env (rho 2))
      (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hG : ForcingLabelPermutations.Carrier (env I) (env G)) (hF : ForcingSupportFilter.Filter (env I) (env G) (env mu) (env F))
    (hLabelMap : ForcingConditionGraphs.FunctionOn (env K) (env labelMap))
    (hTop : ForcingWithTopCarrier.Empty (env top))
    (hLabels : ForcingLabelSet.LabelSet (env (rho 6)) (env I) (env K) (env labelMap) (env top) (env bit) (env labels))
    (hLabelBound : ForcingLabelBound.LabelBound (env (rho 6)) (env I) (env K) (env labelMap) (env top) (env bit) (env bound))
    (hq : Injection (env (rho 0)) (env I) (env q))
    (hAq : ForcingSupportedNames.Range (env (rho 0)) (env q) (env Aq))
    (hHq : ForcingLabelPermutations.Fixing (env G) (env Aq) (env Hq))
    (hE : ForcingSupportedNames.Supported (fun j => env (rho j)) (env Hq) (env E))
    (hVertices : ConstructionComponentCarrier.Carrier (env (rho 0)) (env I) (env mul) (env q) (env vertices))
    (hChain : Chain (env w) (env (rho 0)) (env I) (env mul) (env q) (env zero) (env root) (env vertices) (env chain))
    (hd : ForcingCohenConditions.Condition (env (rho 2)) (env w) (env d))
    (hRoot : Code (env root) (env r) (env index) (env U))
    (hCard : ConstructionSaturationCardinals.Cardinals hM (env (rho 0)) (env mul) (env mark) (env mu))
    (hmark : (Project.FirstOrderSemantics.reduct M).mem (env mark) (env (rho 0)))
    (hEHS : ForcingHS.HS ForcingProductFamily.actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) (env E))
    (hCoord : ForcingCohenCoordinates.Cartesian (env (rho 0)) (env K) (env coordS))
    (hLocal : ForcingCohenCoordinates.Cartesian (env coordS) (env B) (env localS))
    (hCodes : ForcingTailCodes.Carrier (fun j => env (rho j)) (env G) (env F) (env bound) (env w) (env names) (env chain) (env codes))
    (hRange : ForcingStabilizerTransport.Image (env r) (env (rho 0)) (env Ar))
    (hFix : ForcingLabelPermutations.Fixing (env G) (env Ar) (env Hr))
    (hIncl : (Project.FirstOrderSemantics.reduct M).MemberSubset (env Hr) (env support))
    (hFamily : ForcingOrdinalFixed.FixedFamily (fun j => env (rho j)) (env G) (env F) (env support) (env codes) (env ranks))
    (hSelection : ForcingCollectedName.Collected (ForcingCohenSelection.liftRelation
      (ForcingCodeSelection.relation rho I G F mul q bound labels E root w chain codes order) id (rho 0) I (rho 2) w)
      env (env codes) (env ranks) (env (rho 6)) (env selection))
    (hz0 : ForcingSupportingRoot.Code (env z0) (env d) (env r))
    (hTheta : ForcingCheckName.Checked (env top) (env theta) (env ntheta))
    (hEq : ForcingAtomicRelations.Forces true (orderFormula (rho 0) mul) env (env (rho 6)) (env selection) (env ntheta) (env z0)) :
    ∀ beta, (Project.FirstOrderSemantics.reduct M).mem beta (env theta) →
      ∃ f rec, ForcingPowerName.Subset (env d) f ∧ Record env rho w I K G F mul labelMap top bit labels bound E q root chain r localS codes order ranks f rec beta := by
  intro beta hbt
  obtain ⟨nb,hBeta⟩ := ForcingCheckName.exists_checked hM (env top) beta
  obtain ⟨a,rankName,zr,f,tau,s,m,x,j,label,name,z,pb,inner,rec,ha,han,hzr,hRank,hf,hdf,hSel,hEntry,hLinks,hs,hmD,hSub,hx,hxj,hj,hLabel,hName,hClass,hz,hForce,hSupport,hpb,hPullback,hInner,hRec⟩ :=
    ForcingCodeRecordWitness.member_record_at hM hChoice env rho w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq zero root vertices chain names r index U coordS localS codes order Ar Hr support ranks selection d z0 theta ntheta beta nb
      hw hMu hI hSmall hMergers hRow hm hJ hp hG hF hLabelMap hTop hLabels hLabelBound hq hAq hHq hE
      hVertices hChain hd hRoot hCard hmark hEHS hCoord hLocal hCodes hRange hFix hIncl hFamily hSelection
      hz0 hTheta hBeta hbt hEq
  refine ⟨f,rec,hdf,a,rankName,nb,zr,tau,s,m,x,j,name,z,pb,inner,ha,han,hBeta,hzr,hRank,hf,hSel,hEntry,hLinks,hs,hmD,hSub,hx,hxj,?_,hz,hForce,hSupport,hpb,hPullback,hInner,hRec⟩
  exact (ForcingRelationClassMove.family_semantics env rho G F mul I K labelMap top bit labels E j name).mpr
    ⟨hj,hName,label,hLabel,hClass⟩


def Graph {k : Nat} (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k)
    (w I K G F mul labelMap top bit labels bound E q root chain r localS codes order ranks : Fin k) (Records theta relation : M.Carrier .set) : Prop :=
  ∀ p rec beta, (∃ inner, PureKuratowski.Code M inner rec beta ∧ PureKuratowski.PairMember M p inner relation) ↔
    (Project.FirstOrderSemantics.reduct M).mem p (env (rho 3)) ∧
    (Project.FirstOrderSemantics.reduct M).mem rec Records ∧
    (Project.FirstOrderSemantics.reduct M).mem beta theta ∧ Record env rho w I K G F mul labelMap top bit labels bound E q root chain r localS codes order ranks p rec beta

theorem exists_graph (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (w I K G F mul labelMap top bit labels bound E q root chain r localS codes order ranks : Fin k)
    (Records theta : M.Carrier .set) : ∃ relation, Graph env rho w I K G F mul labelMap top bit labels bound E q root chain r localS codes order ranks Records theta relation := by
  have hZF := ModelTransfer.project_models_iff.mp hM
  let pair := KuratowskiZF.interpretation hM
  obtain ⟨values,hValues⟩ := ZF.exists_cartesianProduct hZF pair Records theta
  obtain ⟨triples,hTriples⟩ := ZF.exists_cartesianProduct hZF pair (env (rho 3)) values
  let penv : Env (Project.FirstOrderSemantics.reduct M) k := ⟨env,fun _ => Records⟩
  let schema : Project.UnarySchema k := {
    body := .existsE (.existsE (.existsE (.existsE
      (.conj (ProjectSyntax.encode id (PairSyntax.ordered 4 3 0))
        (.conj (ProjectSyntax.encode id (PairSyntax.ordered 0 2 1))
          (record rho w I K G F mul labelMap top bit labels bound E q root chain r localS codes order ranks (fun i => i.succ.succ.succ.succ.succ) 3 2 1))))))
    freeClosed := by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,record_freeClosed] }
  have he t : schema.denote penv t ↔ ∃ d rec beta inner,
      PureKuratowski.Code M t d inner ∧ PureKuratowski.Code M inner rec beta ∧ Record env rho w I K G F mul labelMap top bit labels bound E q root chain r localS codes order ranks d rec beta := by
    simp only [schema,Project.UnarySchema.denote,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
      GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_code,record_semantics hM]
    rfl
  obtain ⟨relation,hRelation⟩ := ZF.separation_exists_d hZF schema penv triples
  refine ⟨relation,fun d rec beta => ⟨?_,?_⟩⟩
  · rintro ⟨inner,hInner,t,ht,htR⟩
    obtain ⟨htT,htPhi⟩ := (hRelation t).mp htR
    obtain ⟨d',hd,inner',hi,ht'⟩ := (hTriples t).mp htT
    obtain ⟨rfl,rfl⟩ := PureKuratowski.code_injective ht ht'
    obtain ⟨rec',hr,beta',hb,hI'⟩ := (hValues inner).mp hi
    obtain ⟨rfl,rfl⟩ := PureKuratowski.code_injective hInner hI'
    obtain ⟨d'',rec'',beta'',inner'',ht'',hI'',hRecord⟩ := (he t).mp htPhi
    obtain ⟨rfl,rfl⟩ := PureKuratowski.code_injective ht ht''
    obtain ⟨rfl,rfl⟩ := PureKuratowski.code_injective hInner hI''
    exact ⟨hd,hr,hb,hRecord⟩
  · rintro ⟨hd,hr,hb,hRecord⟩
    obtain ⟨inner,hInner⟩ := pair.total rec beta
    obtain ⟨t,ht⟩ := pair.total d inner
    exact ⟨inner,hInner,t,ht,(hRelation t).mpr
      ⟨(hTriples t).mpr ⟨d,hd,inner,(hValues inner).mpr ⟨rec,hr,beta,hb,hInner⟩,ht⟩,
        (he t).mpr ⟨d,rec,beta,inner,ht,hInner,hRecord⟩⟩⟩

private theorem record_typed {k : Nat} {env : Fin k → M.Carrier .set} {rho : Fin 7 → Fin k}
    {w I K G F mul labelMap top bit labels bound E q root chain r localS codes order ranks : Fin k} {localP Inner Records p rec beta : M.Carrier .set}
    (hP : ForcingCohenConditions.Carrier (env localS) (env w) localP)
    (hInner : ForcingCohenCoordinates.Cartesian (env (rho 0)) localP Inner)
    (hRecords : ForcingCohenCoordinates.Cartesian (env (rho 0)) Inner Records)
    (h : Record env rho w I K G F mul labelMap top bit labels bound E q root chain r localS codes order ranks p rec beta) :
    ForcingCohenConditions.Condition (env (rho 2)) (env w) p ∧ (Project.FirstOrderSemantics.reduct M).mem rec Records := by
  obtain ⟨a,n,nb,zr,tau,s,m,x,j,name,z,pb,inner,_,_,_,_,_,hd,_,_,_,_,hm,_,hx,_,_,_,_,_,hpb,_,hi,hr⟩ := h
  exact ⟨hd,(hRecords rec).mpr ⟨m,hm,inner,(hInner inner).mpr ⟨x,hx,pb,(hP pb).mpr hpb,hi⟩,hr⟩⟩

theorem ordinalType_cardinal_le (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M))
    (hZFC : (Project.FirstOrderSemantics.reduct M).Models SetTheory.ZFC) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k)
    (w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq zero root vertices chain names r index U coordS localS codes order Ar Hr support ranks selection d z0 theta ntheta : Fin k)
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega (env w))
    (hMu : (Project.FirstOrderSemantics.reduct M).IsInfiniteCardinal (KuratowskiZF.interpretation hM) (env w) (env mu))
    (hI : (Project.FirstOrderSemantics.reduct M).IsHartogsNumber (KuratowskiZF.interpretation hM) (env I) (env mu))
    (hSmall : ForcingSupportSize.Small (env (rho 0)) (env mu))
    (hMergers : ConstructionSaturationMergers.AllMergers (env w) (env history) (env kappa))
    (hRow : ConstructionTowerHistory.Row (env history) (env kappa) (env (rho 0)) (env mul) (env one) (env mark) (env H) (env C) (env incoming) (env base) (env kappa))
    (hm : ForcingDiagramPoset.LeftCancelMonoid (env (rho 0)) (env mul) (env one))
    (hJ : ConstructionProbeSharedIntersections.ConditionalJoins (env (rho 0)) (env mul))
    (hp : ForcingProductFamily.Presentation (env (rho 0)) (env I) (env K) (env B) (env w) (env (rho 1)) (env (rho 2))
      (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hG : ForcingLabelPermutations.Carrier (env I) (env G)) (hF : ForcingSupportFilter.Filter (env I) (env G) (env mu) (env F))
    (hLabelMap : ForcingConditionGraphs.FunctionOn (env K) (env labelMap))
    (hTop : ForcingWithTopCarrier.Empty (env top))
    (hLabels : ForcingLabelSet.LabelSet (env (rho 6)) (env I) (env K) (env labelMap) (env top) (env bit) (env labels))
    (hLabelBound : ForcingLabelBound.LabelBound (env (rho 6)) (env I) (env K) (env labelMap) (env top) (env bit) (env bound))
    (hq : Injection (env (rho 0)) (env I) (env q))
    (hAq : ForcingSupportedNames.Range (env (rho 0)) (env q) (env Aq))
    (hHq : ForcingLabelPermutations.Fixing (env G) (env Aq) (env Hq))
    (hE : ForcingSupportedNames.Supported (fun j => env (rho j)) (env Hq) (env E))
    (hVertices : ConstructionComponentCarrier.Carrier (env (rho 0)) (env I) (env mul) (env q) (env vertices))
    (hChain : Chain (env w) (env (rho 0)) (env I) (env mul) (env q) (env zero) (env root) (env vertices) (env chain))
    (hd : ForcingCohenConditions.Condition (env (rho 2)) (env w) (env d))
    (hRoot : Code (env root) (env r) (env index) (env U))
    (hCard : ConstructionSaturationCardinals.Cardinals hM (env (rho 0)) (env mul) (env mark) (env mu))
    (hmark : (Project.FirstOrderSemantics.reduct M).mem (env mark) (env (rho 0)))
    (hEHS : ForcingHS.HS ForcingProductFamily.actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) (env E))
    (hCoord : ForcingCohenCoordinates.Cartesian (env (rho 0)) (env K) (env coordS))
    (hLocal : ForcingCohenCoordinates.Cartesian (env coordS) (env B) (env localS))
    (hCodes : ForcingTailCodes.Carrier (fun j => env (rho j)) (env G) (env F) (env bound) (env w) (env names) (env chain) (env codes))
    (hRange : ForcingStabilizerTransport.Image (env r) (env (rho 0)) (env Ar))
    (hFix : ForcingLabelPermutations.Fixing (env G) (env Ar) (env Hr))
    (hIncl : (Project.FirstOrderSemantics.reduct M).MemberSubset (env Hr) (env support))
    (hFamily : ForcingOrdinalFixed.FixedFamily (fun j => env (rho j)) (env G) (env F) (env support) (env codes) (env ranks))
    (hSelection : ForcingCollectedName.Collected (ForcingCohenSelection.liftRelation
      (ForcingCodeSelection.relation rho I G F mul q bound labels E root w chain codes order) id (rho 0) I (rho 2) w)
      env (env codes) (env ranks) (env (rho 6)) (env selection))
    (hz0 : ForcingSupportingRoot.Code (env z0) (env d) (env r))
    (hTheta : ForcingCheckName.Checked (env top) (env theta) (env ntheta))
    (hEq : ForcingAtomicRelations.Forces true (orderFormula (rho 0) mul) env (env (rho 6)) (env selection) (env ntheta) (env z0))
    (hWO : (Project.FirstOrderSemantics.reduct M).IsSetCodedWellOrder (KuratowskiZF.interpretation hM) (env order) (env codes))
    (hRanks : ForcingConditionGraphs.FunctionOn (env codes) (env ranks))
    (hPow : (Project.FirstOrderSemantics.reduct M).IsCardinalExponentiation (KuratowskiZF.interpretation hM) (env mu) (env mu) (env w))
    (hK : (Project.FirstOrderSemantics.reduct M).CardinalLessOrEqual (KuratowskiZF.interpretation hM) (env K) (env mu))
    (hTwo : ∃ o, (Project.FirstOrderSemantics.reduct M).IsOrdinalOne o ∧ (Project.FirstOrderSemantics.reduct M).SuccessorOf (env B) o) :
    (Project.FirstOrderSemantics.reduct M).CardinalLessOrEqual (KuratowskiZF.interpretation hM) (env theta) (env mu) := by
  have hZF := ModelTransfer.project_models_iff.mp hM
  let pair := KuratowskiZF.interpretation hM
  obtain ⟨Power,hPower⟩ := ZF.exists_functionSpace hZF pair (env w) (env mu)
  obtain ⟨Pmu,hPmu⟩ := (ConstructionConcreteCardinals.normalize_power hM hPow hPower).2.symm hZF pair
  obtain ⟨localP,hLocalP⟩ := ForcingCohenConditions.exists_carrier hM (env localS) (env w)
  obtain ⟨Inner,Records,hInner,hRecords,hRecordsMu⟩ := ForcingCohenCounting.records_bound hM hZFC hw hMu hPower ⟨Pmu,hPmu.1⟩
    ((ForcingSupportSize.native_small hM (env (rho 0)) (env mu)).mp hSmall) hK hTwo hCoord hLocal hLocalP
  obtain ⟨relation,hRel⟩ := exists_graph hM env rho w I K G F mul labelMap top bit labels bound E q root chain r localS codes order ranks Records (env theta)
  obtain ⟨compat,hCompat⟩ := ForcingCohenChainBound.exists_graph hM (env (rho 3))
  have hChainBound := ForcingCohenChainBound.chain_bound hM hZFC hw hMu hPower ⟨Pmu,hPmu.1⟩ hTwo hp.2.1 hp.2.2.1 hCompat
  have htotal beta (hb : (Project.FirstOrderSemantics.reduct M).mem beta (env theta)) :
      ∃ rec, (Project.FirstOrderSemantics.reduct M).mem rec Records ∧
        ∃ p, (Project.FirstOrderSemantics.reduct M).mem p (env (rho 3)) ∧ ForcingChainBound.Values pair relation p rec beta := by
    obtain ⟨p,rec,_,hRecord⟩ := total hM hChoice env rho w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq zero root vertices chain names r index U coordS localS codes order Ar Hr support ranks selection d z0 theta ntheta
      hw hMu hI hSmall hMergers hRow hm hJ hp hG hF hLabelMap hTop hLabels hLabelBound hq hAq hHq hE
      hVertices hChain hd hRoot hCard hmark hEHS hCoord hLocal hCodes hRange hFix hIncl hFamily hSelection
      hz0 hTheta hEq beta hb
    have hTyped := record_typed hLocalP hInner hRecords hRecord
    have hpP := (hp.2.2.1 p).mpr hTyped.1
    exact ⟨rec,hTyped.2,p,hpP,(hRel p rec beta).mpr ⟨hpP,hTyped.2,hb,hRecord⟩⟩
  have hsingle rec beta gamma p p' (_hr : (Project.FirstOrderSemantics.reduct M).mem rec Records)
      (_hb : (Project.FirstOrderSemantics.reduct M).mem beta (env theta))
      (_hg : (Project.FirstOrderSemantics.reduct M).mem gamma (env theta))
      (_hp : (Project.FirstOrderSemantics.reduct M).mem p (env (rho 3)))
      (_hp' : (Project.FirstOrderSemantics.reduct M).mem p' (env (rho 3)))
      (hR : ForcingChainBound.Values pair relation p rec beta) (hR' : ForcingChainBound.Values pair relation p' rec gamma)
      (hc : PureKuratowski.PairMember M p p' compat) : beta = gamma :=
    single hM hChoice env rho w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq zero root vertices chain names r index U Ar Hr localS codes order ranks
      hw hMu hI hSmall hMergers hRow hm hp hG hF hLabelMap hTop hLabels hAq hHq hE hChain hRoot hCodes hRange hFix hWO hRanks
      ((hRel p rec beta).mp hR).2.2.2 ((hRel p' rec gamma).mp hR').2.2.2 ((hCompat p p').mp hc).2.2
  obtain ⟨product,hProduct⟩ := ZF.exists_cartesianProduct hZF pair Records (env mu)
  obtain ⟨j,hj⟩ := ForcingChainBound.cardinal_le_mul pair hZFC (ForcingCohenChainBound.graph_refl hp.2.2.1 hCompat)
    hChainBound htotal hsingle hProduct
  obtain ⟨idMu,hIdMu⟩ := ZF.exists_identityBijection hZF pair (env mu)
  obtain ⟨g,hg⟩ := ExistingCardinalBounds.infinite_product_l pair hZF hw hMu hRecordsMu ⟨idMu,hIdMu.1⟩ hProduct
  exact ZF.exists_compositionInjection hZF pair hj hg

def boundSentence {k : Nat} (rho : Fin 7 → Fin k)
    (w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq zero root vertices chain names r index U coordS localS codes order Ar Hr support ranks selection d z0 theta ntheta : Fin k) : Project.Sentence where
  formula := Project.Formula.forallClosure k
    (.imp (Project.Formula.isOmega (.bound w))
    (.imp (Project.Formula.isInfiniteCardinal PureKuratowskiProject.convention (.bound w) (.bound mu))
    (.imp (ConstructionSaturationIndex.hartogs mu I)
    (.imp (ProjectSyntax.encode id (ForcingSupportSize.small (rho 0) mu))
    (.imp (ConstructionSaturationMergers.allMergers w history kappa)
    (.imp (ConstructionTowerHistory.row history kappa (rho 0) mul one mark H C incoming base kappa)
    (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid (rho 0) mul one))
    (.imp (ConstructionProbeSharedIntersections.conditionalJoins (rho 0) mul)
    (.imp (ProjectSyntax.encode id (ForcingProductFamily.presentation (rho 0) I K B w (rho 1) (rho 2) (rho 3) (rho 4) (rho 5) (rho 6)))
    (.imp (ProjectSyntax.encode id (ForcingLabelPermutations.carrier I G))
    (.imp (ProjectSyntax.encode id (ForcingSupportFilter.filter I G mu F))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.functionOn labelMap K))
    (.imp (ProjectSyntax.encode id (ForcingWithTopCarrier.empty top))
    (.imp (ProjectSyntax.encode id (ForcingLabelSet.labelSet (rho 6) I K labelMap top bit labels))
    (.imp (ProjectSyntax.encode id (ForcingLabelBound.labelBound (rho 6) I K labelMap top bit bound))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.injection q (rho 0) I))
    (.imp (ProjectSyntax.encode id (ForcingSupportedNames.range (rho 0) q Aq))
    (.imp (ProjectSyntax.encode id (ForcingLabelPermutations.fixing G Aq Hq))
    (.imp (ProjectSyntax.encode id (ForcingEquivariantMix.fixedAll rho Hq E))
    (.imp (ConstructionComponentCarrier.carrier (rho 0) I mul q vertices)
    (.imp (ConstructionComponentCofinal.chain w (rho 0) I mul q zero root vertices chain)
    (.imp (ProjectSyntax.encode id (ForcingCohenConditions.condition (rho 2) w d))
    (.imp (ConstructionComponentCarrier.code root r index U)
    (.imp (ConstructionSaturationCardinals.cardinalsF (rho 0) mul mark mu)
    (.imp (.mem (.bound mark) (.bound (rho 0)))
    (.imp (ProjectSyntax.encode id (ForcingHS.hs ForcingProductFamily.actionFormula rho G (rho 6) F E))
    (.imp (ProjectSyntax.encode id (ForcingCohenCoordinates.cartesian (rho 0) K coordS))
    (.imp (ProjectSyntax.encode id (ForcingCohenCoordinates.cartesian coordS B localS))
    (.imp (ForcingTailCodes.carrier rho G F bound w names chain codes)
    (.imp (ProjectSyntax.encode id (ForcingStabilizerTransport.image r (rho 0) Ar))
    (.imp (ProjectSyntax.encode id (ForcingLabelPermutations.fixing G Ar Hr))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.subset Hr support))
    (.imp (ProjectSyntax.encode id (ForcingOrdinalFixed.fixedFamily rho G F support codes ranks))
    (.imp (ProjectSyntax.encode id (ForcingCollectedName.collected (ForcingCohenSelection.liftRelation (ForcingCodeSelection.relation rho I G F mul q bound labels E root w chain codes order) id (rho 0) I (rho 2) w) id codes ranks (rho 6) selection))
    (.imp (ProjectSyntax.encode id (ForcingSupportingRoot.code z0 d r))
    (.imp (ProjectSyntax.encode id (ForcingCheckName.checkName top theta ntheta))
    (.imp (ProjectSyntax.encode id (ForcingAtomicRelations.forces true (orderFormula (rho 0) mul) id (rho 6) selection ntheta z0))
    (.imp (Project.Formula.isSetCodedWellOrder PureKuratowskiProject.convention (.bound order) (.bound codes))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.functionOn ranks codes))
    (.imp (Project.Formula.isCardinalExponentiation PureKuratowskiProject.convention (.bound mu) (.bound mu) (.bound w))
    (.imp (Project.Formula.cardinalLessOrEqual PureKuratowskiProject.convention (.bound K) (.bound mu))
    (.imp (ForcingProductParameters.two B)
    (Project.Formula.cardinalLessOrEqual PureKuratowskiProject.convention (.bound theta) (.bound mu))))))))))))))))))))))))))))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
      ConstructionSaturationIndex.hartogs_freeClosed,ConstructionSaturationMergers.allMergers_freeClosed,
      ConstructionTowerHistory.row_freeClosed,ConstructionProbeSharedIntersections.conditionalJoins_freeClosed,
      ConstructionComponentCarrier.carrier_freeClosed,ConstructionComponentCofinal.chain_freeClosed,
      ConstructionComponentCarrier.code_freeClosed,ConstructionSaturationCardinals.cardinalsF_freeClosed,
      ForcingTailCodes.carrier_freeClosed,Project.Formula.isCardinalExponentiation,
      Project.Formula.isFunctionSpace,ForcingProductParameters.two_freeClosed]

theorem bound_models {k : Nat} (rho : Fin 7 → Fin k)
    (w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq zero root vertices chain names r index U coordS localS codes order Ar Hr support ranks selection d z0 theta ntheta : Fin k)
    (hM : FirstOrder.Theory.Models M nativeZF) (hChoice : ConstructionDirectedCardinality.Choice (M := M))
    (hZFC : (Project.FirstOrderSemantics.reduct M).Models SetTheory.ZFC) :
    (Project.fo_sentence (boundSentence rho w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq zero root vertices chain names r index U coordS localS codes order Ar Hr support ranks selection d z0 theta ntheta)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM),SetTheory.Structure.satisfiesSentence_iff]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro env
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    Project.Formula.satisfies_isOmega_iff,
    Project.Formula.satisfies_isInfiniteCardinal_iff (KuratowskiZF.interpretation hM) (ModelTransfer.extensionality hM),
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ConstructionSaturationIndex.hartogs_semantics hM,ForcingSupportSize.small_semantics (M := M),
    ConstructionSaturationMergers.allMergers_semantics hM,ConstructionTowerHistory.row_semantics hM,
    ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),ConstructionProbeSharedIntersections.conditionalJoins_semantics hM,
    ForcingProductFamily.presentation_semantics (M := M),ForcingLabelPermutations.carrier_semantics (M := M),
    ForcingSupportFilter.filter_semantics (M := M),ForcingConditionGraphs.functionOn_semantics (M := M),
    ForcingWithTopCarrier.empty_semantics (M := M),ForcingLabelSet.labelSet_semantics (M := M),
    ForcingLabelBound.labelBound_semantics (M := M),ForcingSupportSize.injection_semantics (M := M),
    ForcingSupportedNames.range_semantics (M := M),ForcingLabelPermutations.fixing_semantics (M := M),
    ForcingSupportedNames.supported_semantics (M := M),ConstructionComponentCarrier.carrier_semantics hM,
    ConstructionComponentCofinal.chain_semantics hM,ForcingCohenConditions.condition_semantics (M := M),
    ConstructionComponentCarrier.code_semantics hM,ConstructionSaturationCardinals.cardinalsF_semantics hM,
    ForcingHS.hs_semantics (M := M),ForcingCohenCoordinates.cartesian_semantics (M := M),ForcingTailCodes.carrier_semantics hM,
    ForcingStabilizerTransport.image_semantics (M := M),ForcingLabelPermutations.subset_semantics (M := M),
    ForcingOrdinalFixed.fixedFamily_semantics (M := M),ForcingCollectedName.collected_semantics (M := M),
    ForcingSupportingRoot.code_semantics (M := M),ForcingCheckName.checkName_semantics (M := M),ForcingAtomicRelations.forces_semantics (M := M),
    Project.Formula.satisfies_isSetCodedWellOrder_iff (KuratowskiZF.interpretation hM),
    Project.Formula.satisfies_isCardinalExponentiation_iff (KuratowskiZF.interpretation hM) (ModelTransfer.extensionality hM),
    Project.Formula.satisfies_cardinalLessOrEqual_iff (KuratowskiZF.interpretation hM) (ModelTransfer.extensionality hM),
    ForcingProductParameters.two_semantics]
  intros
  exact ordinalType_cardinal_le hM hChoice hZFC env rho w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq zero root vertices chain names r index U coordS localS codes order Ar Hr support ranks selection d z0 theta ntheta ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›

theorem bound_kernel_certificate {k : Nat} (rho : Fin 7 → Fin k)
    (w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq zero root vertices chain names r index U coordS localS codes order Ar Hr support ranks selection d z0 theta ntheta : Fin k) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (ConstructibleGround.relative
      (boundSentence rho w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq zero root vertices chain names r index U coordS localS codes order Ar Hr support ranks selection d z0 theta ntheta))) := by
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
    (bound_models rho w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq zero root vertices chain names r index U coordS localS codes order Ar Hr support ranks selection d z0 theta ntheta hL hChoice
      (InnerModel.l_model_zfc_l (ModelTransfer.project_models_iff.mp hN)))


end PPAC.Migration.ForcingCodeCardinals
