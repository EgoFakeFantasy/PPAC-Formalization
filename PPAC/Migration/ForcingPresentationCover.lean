/- Pinned OrdinalPresentation.presentationPartial_cover and ordinal_presentation.
Use the ACTUAL full record/function family, existing name support-filter basis,
diagram extension and orbit identity copy. Coverage is a proof output. -/
import PPAC.Migration.ForcingPresentationFamily
import PPAC.Migration.ForcingActualOrdinalChoice

namespace PPAC.Migration.ForcingPresentationCover
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open Source (Formula)
open Source.SetLanguage (args3)
open ForcingProductFamily (Presentation actionFormula mapRel_action)
open ForcingMapConditions (MapRel)
open ForcingProductSymmetry (orderFormula orderFormula_semantics)
open ForcingPairUnion (domain domain_semantics)
open ForcingSupportSize (Small Injection)
open ForcingHS (HS)
open ForcingSupportedNames (Supported)
open ForcingFormula (Force)
open ForcingAtomicRelations (Forces)
open ForcingPresentationFamily (Family Record)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 1600000
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

/-- Every member, at EVERY stronger condition, is reached by one of the
actual family values. The supporting diagram is constructed below the witness
condition, exactly as in source; no generic filter or rank bound is involved. -/
theorem cover (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k)
    (w mu I K B G F mul one mark top c hi X labels : Fin k) {indices f p : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega (env w))
    (hMu : (Project.FirstOrderSemantics.reduct M).IsInfiniteCardinal (KuratowskiZF.interpretation hM) (env w) (env mu))
    (hI : (Project.FirstOrderSemantics.reduct M).IsHartogsNumber (KuratowskiZF.interpretation hM) (env I) (env mu))
    (hD : Small (env (rho 0)) (env mu))
    (hCard : ConstructionSaturationCardinals.Cardinals hM (env (rho 0)) (env mul) (env mark) (env mu))
    (hm : ForcingDiagramPoset.LeftCancelMonoid (env (rho 0)) (env mul) (env one))
    (hMark : (Project.FirstOrderSemantics.reduct M).mem (env mark) (env (rho 0)))
    (hPres : Presentation (env (rho 0)) (env I) (env K) (env B) (env w) (env (rho 1)) (env (rho 2))
      (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hG : ForcingLabelPermutations.Carrier (env I) (env G))
    (hFilter : ForcingSupportFilter.Filter (env I) (env G) (env mu) (env F))
    (ht : ForcingWithTopCarrier.Empty (env top))
    (hX : HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) (env X))
    (hLabels : ForcingLabelSet.LabelSet (env (rho 6)) (env I) (env K) (env c) (env top) (env hi) (env labels))
    (hLabelsHS : HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) (env labels))
    (hFamily : Family (orderFormula (rho 0) mul) (domain rho G F) env (fun j => env (rho j))
      (env I) (env K) (env G) (env F) (env top) (env one) (env c) (env hi) (env X) indices f) :
    ForcingCompletionGraph.Cover (orderFormula (rho 0) mul) (domain rho G F) env (env (rho 6)) indices f (env labels) (env X) p := by
  let hZF := ModelTransfer.project_models_iff.mp hM
  let pair := KuratowskiZF.interpretation hM
  let R := orderFormula (rho 0) mul
  let Hdom := domain rho G F
  let W := env (rho 6)
  let v7 : Fin 7 → M.Carrier .set := fun j => env (rho j)
  have hpre := ForcingProductPoset.preorder env (rho 0) mul (rho 6) hm
    hPres.2.2.2.2.1 hPres.2.2.2.1 hPres.2.2.2.2.2
  have hNormal := ForcingNormalFilter.is_normal hM hw hMu hG hFilter
  have hLarge : ¬ Small (env I) (env mu) := fun h => hI.not_cardinalLessOrEqual (ZF.modelsKP hZF)
    ((ForcingSupportSize.native_small hM _ _).mp h)
  obtain ⟨idMu,hIdMu⟩ := ZF.exists_inclusionInjection hZF pair (fun _ h => h :
    (Project.FirstOrderSemantics.reduct M).MemberSubset (env mu) (env mu))
  have hMuI := (hI.2 (env mu) hMu.1.1).mpr ⟨idMu,hIdMu⟩
  obtain ⟨muToI,hMuToI⟩ := ZF.exists_inclusionInjection hZF pair
    (fun x hx => hI.1.transitive (env mu) hMuI x hx)
  obtain ⟨toMu,hToMu⟩ := (ForcingSupportSize.native_small hM _ _).mp hD
  obtain ⟨root,hRoot⟩ := ZF.exists_compositionInjection hZF pair hToMu hMuToI
  have hRoot' := (ForcingSupportSize.native_injection hM _ _ root).mpr hRoot
  have htW := (hPres.2.2.2.2.2 (env top)).mpr (Or.inl ht)
  have hEmptyCohen : ForcingCohenConditions.Condition (env (rho 2)) (env w) (env top) := ForcingCohenCodes.empty_condition hM ht
  intro y _hy q hq _hqp hY r hr hrq
  obtain ⟨t,sigma,b,htP,htr,_hb,hEdge,_htb,hYsigma⟩ :=
    ((ForcingAtomicRelations.mem_iff hM R env W y (env X) q).mp hY).2 r hr hrq
  have hSigma := ForcingHS.child hX hEdge
  obtain ⟨stabilizer,hStabilizer,hStabilizerF⟩ := ForcingHS.symmetric_of_hs hSigma
  obtain ⟨_,J,HJ,hJI,hJSmall,hFixJ,hIncluded⟩ := (hFilter stabilizer).mp hStabilizerF
  have hSigmaJ : Supported v7 HJ sigma := by
    intro pi hpi act hAct
    obtain ⟨a,ha,hFixed⟩ := ((hStabilizer pi).mp (hIncluded pi hpi)).2
    have e := ForcingProductFamily.unique hM ((mapRel_action v7 pi a).mp ha) ((mapRel_action v7 pi act).mp hAct)
    exact e ▸ hFixed
  obtain ⟨d,s,z,hd,hs,hZ,hZt⟩ := ForcingLabelDensity.exists_condition_below hM hPres hm hRoot' htP
  have hzW := ForcingSupportingRoot.code_mem hPres hd hs hZ
  have hzt := (orderFormula_semantics env (rho 0) mul z t).mpr hZt
  obtain ⟨newRoot,hNewRoot,hSub,hCover⟩ := ConstructionDiagramCoverage.extend_through hM hChoice hw hMu hLarge hCard
    (hm.2.1 (env mark) hMark) hs hJI hJSmall
  obtain ⟨JP,hJP,_hJPI,_hJPSmall⟩ := ConstructionDescentPlacement.diagram_range hM hMu.1.1 hNewRoot hD
  obtain ⟨HP,hHP⟩ := ForcingLabelPermutations.exists_fixing hM (env G) JP
  have hSigmaP : Supported v7 HP sigma := ForcingSupportedNames.supported_mono hFixJ hHP
    (fun x hx => (hJP x).mpr (hCover x hx)) hSigmaJ
  obtain ⟨edge,hEdgeCode,hEdgeMem⟩ := hEdge
  obtain ⟨i,hRecordCode⟩ := KuratowskiZF.exists_code hM edge newRoot
  have hRecord : Record v7 (env I) (env G) (env X) i sigma b newRoot :=
    ⟨edge,hEdgeMem,hRecordCode,hEdgeCode,hNewRoot,JP,hJP,HP,hHP,hSigmaP⟩
  have hiIndex := (hFamily.1 i).mpr ⟨sigma,b,newRoot,hRecord⟩
  obtain ⟨fi,hif,_hUniqueValue⟩ := hFamily.2.1.2 i hiIndex
  obtain ⟨_hi,sigma',b',newRoot',hRecord',j,a,left,seed,hCenter,hActivation,hLabel,hPair,hGraph,_hFiHS,_hFiFixed,_hFiUnique⟩ :=
    (hFamily.2.2 i fi).mp hif
  obtain ⟨es,eb,er⟩ := ForcingPresentationFamily.record_unique hRecord hRecord'
  cases es
  cases eb
  cases er
  obtain ⟨out,hOut⟩ := ForcingSupportingRoot.exists_code hM d newRoot
  have hOutW := ForcingSupportingRoot.code_mem hPres hd hNewRoot hOut
  have hOutZ := (orderFormula_semantics env (rho 0) mul out z).mpr
    ((ForcingSupportingRoot.code_le hOut hZ).mpr ⟨fun _ h => h,env mark,hMark,hSub⟩)
  have hOutT := hpre.2 out z t hOutW hzW htP hOutZ hzt
  have hOutR := hpre.2 out t r hOutW htP hr hOutT htr
  have haW := ForcingSupportingRoot.code_mem hPres hEmptyCohen hNewRoot hActivation
  have hOutA := (orderFormula_semantics env (rho 0) mul out a).mpr
    ((ForcingSupportingRoot.code_le hOut hActivation).mpr
      ⟨fun x hx => (ht x hx).elim,ForcingDiagramPoset.le_refl hm hNewRoot⟩)
  have hjI := hNewRoot.1.2 (env one) j hCenter
  have hLeftEdge := (ForcingLabelSet.edge_labelSet hM hLabels left (env top)).mpr ⟨rfl,j,hjI,hLabel⟩
  have hLeftHS := ForcingHS.child hLabelsHS hLeftEdge
  have hAppSelf := ForcingPartialOrbitGraph.app_self hM env rho G F mul top hPres hG hNormal ht hpre hPair hGraph hLeftHS hSigma haW
  have hApp := ForcingFormula.mono hM hpre _ _ haW hOutW hOutA hAppSelf
  have hYS := ForcingAtomicBasic.eq_mono hM hpre hOutW hOutT hYsigma
  have hTuple : ∀ j, Forces true R env W (args3 fi left sigma j) (args3 fi left y j) out := by
    intro j
    exact Fin.cases (ForcingAtomicBasic.eq_refl hM hpre fi out hOutW)
      (Fin.cases (ForcingAtomicBasic.eq_refl hM hpre left out hOutW)
        (Fin.cases (ForcingAtomicBasic.eq_symm hM hYS) (fun i => Fin.elim0 i))) j
  have hAppY := (ForcingFormula.tuple_congr hM hpre (Source.SetLanguage.edge (0 : Fin 3) 1 2)
    (args3 fi left sigma) (args3 fi left y) out hOutW hTuple).mp hApp
  exact ⟨out,hOutW,hOutR,i,hiIndex,fi,hif,left,(domain_semantics env rho G F left).mpr hLeftHS,
    ForcingAtomicBasic.mem_of_edge_eq hM hpre htW
      ((orderFormula_semantics env (rho 0) mul out (env top)).mpr (Or.inl ht)) hLeftEdge
      (ForcingAtomicBasic.eq_refl hM hpre left out hOutW),hAppY⟩


/-- Reuse the existing INTERNAL ordinal enumeration and native composition.
Every old value lifts and every new value is an actual old value. This is the
precise role of the source ordinal equivalence in its existential conclusion. -/
theorem reindex (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) {indices f : M.Carrier .set}
    (hf : ForcingConditionGraphs.FunctionOn indices f) :
    ∃ eta g, (Project.FirstOrderSemantics.reduct M).IsOrdinal eta ∧ ForcingConditionGraphs.FunctionOn eta g ∧
      (∀ j fi, PureKuratowski.PairMember M j fi g → ∃ i, (Project.FirstOrderSemantics.reduct M).mem i indices ∧ PureKuratowski.PairMember M i fi f) ∧
      (∀ i fi, (Project.FirstOrderSemantics.reduct M).mem i indices → PureKuratowski.PairMember M i fi f →
        ∃ j, (Project.FirstOrderSemantics.reduct M).mem j eta ∧ PureKuratowski.PairMember M j fi g) := by
  have hZF := ModelTransfer.project_models_iff.mp hM
  let pair := KuratowskiZF.interpretation hM
  obtain ⟨eta,enumeration,hEta,hEnum,hOnto⟩ := ExistingOrdinalEnumeration.ordinal_enum_l
    (ConstructionDirectedCardinality.models_zfc hM hChoice) pair indices
  have hEnum' := (ForcingSupportSize.native_mapsTo hM eta indices enumeration).mpr hEnum
  obtain ⟨bound,hBound⟩ := ForcingMapConditions.coordinate_bound hM f
  have hFn := (ForcingSupportSize.native_mapsTo hM indices bound f).mp ⟨hf,fun i fi he => (hBound i fi he).2⟩
  obtain ⟨g,hg,hEdges⟩ := ZF.exists_compositionFunction hZF pair hEnum hFn
  refine ⟨eta,g,hEta,((ForcingSupportSize.native_mapsTo hM eta bound g).mpr hg).1,?_,?_⟩
  · intro j fi he
    obtain ⟨_hj,i,hji,hif⟩ := (hEdges j fi).mp he
    exact ⟨i,hEnum'.2 j i hji,hif⟩
  · intro i fi hi hif
    obtain ⟨j,hj,hji⟩ := hOnto i hi
    exact ⟨j,hj,(hEdges j fi).mpr ⟨hj,i,hji,hif⟩⟩

def Presented {k : Nat} (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k)
    (I G F mul top labels X x0 : Fin k) (p : M.Carrier .set) : Prop :=
  ∃ eta groundFamily, (Project.FirstOrderSemantics.reduct M).IsOrdinal eta ∧
    ForcingCompletionGraph.Built (Fin.cases groundFamily (Fin.cases eta env)) (fun j => (rho j).succ.succ)
      I.succ.succ G.succ.succ F.succ.succ mul.succ.succ top.succ.succ 1 labels.succ.succ X.succ.succ x0.succ.succ p

/-- Full pinned ordinal_presentation: actual index/family, actual dense cover,
internal ordinal reindexing and the already accepted complete graph constructor.
No index, family, coverage, ordinal enumeration, Cartesian domain or final
surjection is supplied to the theorem. -/
theorem ordinal_presentation (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k)
    (w mu I K B G F mul one mark top values c lo hi X x0 labels : Fin k) {p : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega (env w))
    (hMu : (Project.FirstOrderSemantics.reduct M).IsInfiniteCardinal (KuratowskiZF.interpretation hM) (env w) (env mu))
    (hI : (Project.FirstOrderSemantics.reduct M).IsHartogsNumber (KuratowskiZF.interpretation hM) (env I) (env mu))
    (hD : Small (env (rho 0)) (env mu))
    (hCard : ConstructionSaturationCardinals.Cardinals hM (env (rho 0)) (env mul) (env mark) (env mu))
    (hm : ForcingDiagramPoset.LeftCancelMonoid (env (rho 0)) (env mul) (env one))
    (hMark : (Project.FirstOrderSemantics.reduct M).mem (env mark) (env (rho 0)))
    (hPres : Presentation (env (rho 0)) (env I) (env K) (env B) (env w) (env (rho 1)) (env (rho 2))
      (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hG : ForcingLabelPermutations.Carrier (env I) (env G))
    (hFilter : ForcingSupportFilter.Filter (env I) (env G) (env mu) (env F))
    (hK : ¬ Small (env K) (env w)) (hc : Injection (env K) (env values) (env c))
    (ht : ForcingWithTopCarrier.Empty (env top))
    (hlo : (Project.FirstOrderSemantics.reduct M).mem (env lo) (env B))
    (hhi : (Project.FirstOrderSemantics.reduct M).mem (env hi) (env B)) (hBits : env lo ≠ env hi)
    (hX : HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) (env X))
    (hX0 : HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) (env x0))
    (hLabels : ForcingLabelSet.LabelSet (env (rho 6)) (env I) (env K) (env c) (env top) (env hi) (env labels))
    (hLabelsHS : HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) (env labels))
    (hp : (Project.FirstOrderSemantics.reduct M).mem p (env (rho 6)))
    (hx0 : Forces false (orderFormula (rho 0) mul) env (env (rho 6)) (env x0) (env X) p) :
    Presented env rho I G F mul top labels X x0 p := by
  let R := orderFormula (rho 0) mul
  let Hdom := domain rho G F
  let W := env (rho 6)
  let v7 : Fin 7 → M.Carrier .set := fun j => env (rho j)
  have hNormal := ForcingNormalFilter.is_normal hM hw hMu hG hFilter
  obtain ⟨indices,f,hFamily⟩ := ForcingPresentationFamily.construct hM env rho I K B w G F mul top one values c lo hi X labels
    hPres hG hNormal hm hw hK hc ht hlo hhi hBits hX hLabels hLabelsHS
  have hLaws := ForcingPresentationFamily.family_laws hFamily
  have hCover : ForcingCompletionGraph.Cover R Hdom env W indices f (env labels) (env X) p :=
    cover hM hChoice env rho w mu I K B G F mul one mark top c hi X labels hw hMu hI hD hCard hm hMark
      hPres hG hFilter ht hX hLabels hLabelsHS hFamily
  obtain ⟨eta,g,hEta,hFunction,hForward,hLift⟩ := reindex hM hChoice hFamily.2.1
  have hCoverEta : ForcingCompletionGraph.Cover R Hdom env W eta g (env labels) (env X) p := by
    intro y hy q hq hqp hY r hr hrq
    obtain ⟨s,hs,hsr,i,hi,fi,hif,a,ha,hA,hApp⟩ := hCover y hy q hq hqp hY r hr hrq
    obtain ⟨j,hj,hjf⟩ := hLift i fi hi hif
    exact ⟨s,hs,hsr,j,hj,fi,hjf,a,ha,hA,hApp⟩
  let other : Fin (k+2) → M.Carrier .set := Fin.cases g (Fin.cases eta env)
  let rr : Fin 7 → Fin (k+2) := fun j => (rho j).succ.succ
  have hR : ∀ a b, MapRel R env a b ↔ MapRel (orderFormula (rr 0) mul.succ.succ) other a b := by
    intro a b
    exact (orderFormula_semantics env (rho 0) mul a b).trans (orderFormula_semantics other (rr 0) mul.succ.succ a b).symm
  have hH : ∀ a, ForcingClassEvaluation.Predicate Hdom env a ↔
      ForcingClassEvaluation.Predicate (domain rr G.succ.succ F.succ.succ) other a := by
    intro a
    exact (domain_semantics env rho G F a).trans (domain_semantics other rr G.succ.succ F.succ.succ a).symm
  have hpre := ForcingProductPoset.preorder other (rr 0) mul.succ.succ (rr 6) hm
    hPres.2.2.2.2.1 hPres.2.2.2.1 hPres.2.2.2.2.2
  refine ⟨eta,g,hEta,?_⟩
  apply ForcingCompletionGraph.construct hM other rr I.succ.succ K.succ.succ B.succ.succ w.succ.succ
    G.succ.succ F.succ.succ mul.succ.succ top.succ.succ 1 0 labels.succ.succ X.succ.succ x0.succ.succ
    hPres hG hNormal ht hpre hFunction hLabelsHS hX hX0 ?_ ?_ hp
    ((ForcingSeparation.atomic_congr hR false W (env x0) (env X) p).mp hx0)
    ((ForcingCompletionGraph.cover_congr hR hH W eta g (env labels) (env X) p).mp hCoverEta)
  · intro pi hpi act hAct j fi _hj hjf
    obtain ⟨i,hi,hif⟩ := hForward j fi hjf
    exact hLaws.2.1 i fi hi hif pi hpi act hAct
  · intro j fi _hj hjf
    obtain ⟨i,hi,hif⟩ := hForward j fi hjf
    exact (ForcingCompletionGraph.partialUnique_congr hR hH W fi).mp (hLaws.2.2 i fi hi hif)


/-- Object formula for the actual ground ordinal, check/domain/graph construction
and full forced surjection. Ground-family witnesses remain internal sets. -/
def presentation {k : Nat} (rho : Fin 7 → Fin k) (I G F mul top labels X x0 p : Fin k) : Project.Formula 1 k :=
  .existsE (.existsE (.conj (Project.Formula.isOrdinal (.bound 1))
    (ProjectSyntax.encode id (ForcingCompletionGraph.construction (fun j => (rho j).succ.succ)
      I.succ.succ G.succ.succ F.succ.succ mul.succ.succ top.succ.succ 1
      labels.succ.succ X.succ.succ x0.succ.succ p.succ.succ))))

theorem presentation_freeClosed {k : Nat} (rho : Fin 7 → Fin k) (I G F mul top labels X x0 p : Fin k) :
    (presentation rho I G F mul top labels X x0 p).FreeClosed := by
  simp -implicitDefEqProofs [presentation,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,Project.Formula.isOrdinal]

theorem presentation_semantics (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Env (Project.FirstOrderSemantics.reduct M) k) (rho : Fin 7 → Fin k) (I G F mul top labels X x0 p : Fin k) :
    Project.Formula.satisfies env (presentation rho I G F mul top labels X x0 p) ↔
      Presented env.bound rho I G F mul top labels X x0 (env.bound p) := by
  simp only [presentation,Presented,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_isOrdinal_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ForcingCompletionGraph.construction_semantics,
    SetTheory.Env.push,Fin.cases_succ,id_eq]
  rfl

def sentence {k : Nat} (rho : Fin 7 → Fin k)
    (w mu I K B G F mul one mark top values c lo hi X x0 labels p : Fin k) : Project.Sentence where
  formula := Project.Formula.forallClosure k
    ([Project.Formula.isOmega (.bound w),
      Project.Formula.isInfiniteCardinal PureKuratowskiProject.convention (.bound w) (.bound mu),
      ConstructionSaturationIndex.hartogs mu I,
      ProjectSyntax.encode id (ForcingSupportSize.small (rho 0) mu),
      ConstructionSaturationCardinals.cardinalsF (rho 0) mul mark mu,
      ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid (rho 0) mul one),
      .mem (.bound mark) (.bound (rho 0)),
      ProjectSyntax.encode id (ForcingProductFamily.presentation (rho 0) I K B w (rho 1) (rho 2) (rho 3) (rho 4) (rho 5) (rho 6)),
      ProjectSyntax.encode id (ForcingLabelPermutations.carrier I G),
      ProjectSyntax.encode id (ForcingSupportFilter.filter I G mu F),
      .neg (ProjectSyntax.encode id (ForcingSupportSize.small K w)),
      ProjectSyntax.encode id (Source.SetLanguage.injection c K values),
      ProjectSyntax.encode id (ForcingWithTopCarrier.empty top),
      .mem (.bound lo) (.bound B),.mem (.bound hi) (.bound B),
      .neg (Project.Formula.extensionalEq (.bound lo) (.bound hi)),
      ProjectSyntax.encode id (ForcingHS.hs actionFormula rho G (rho 6) F X),
      ProjectSyntax.encode id (ForcingHS.hs actionFormula rho G (rho 6) F x0),
      ProjectSyntax.encode id (ForcingLabelSet.labelSet (rho 6) I K c top hi labels),
      ProjectSyntax.encode id (ForcingHS.hs actionFormula rho G (rho 6) F labels),
      .mem (.bound p) (.bound (rho 6)),
      ProjectSyntax.encode id (ForcingAtomicRelations.forces false (orderFormula (rho 0) mul) id (rho 6) x0 X p)].foldr Definitional.Formula.imp (presentation rho I G F mul top labels X x0 p))
  freeClosed := by
    simp -implicitDefEqProofs [List.foldr,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
      Project.Formula.isOmega,Project.Formula.isInfiniteCardinal,ConstructionSaturationIndex.hartogs_freeClosed,
      ConstructionSaturationCardinals.cardinalsF_freeClosed,Project.Formula.extensionalEq,presentation_freeClosed]

theorem models {k : Nat} (rho : Fin 7 → Fin k)
    (w mu I K B G F mul one mark top values c lo hi X x0 labels p : Fin k)
    (hM : FirstOrder.Theory.Models M nativeZF) (hChoice : ConstructionDirectedCardinality.Choice (M := M)) :
    (Project.fo_sentence (sentence rho w mu I K B G F mul one mark top values c lo hi X x0 labels p)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM),SetTheory.Structure.satisfiesSentence_iff]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro env
  simp only [List.foldr,Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_isOmega_iff,
    Project.Formula.satisfies_isInfiniteCardinal_iff (KuratowskiZF.interpretation hM) (ModelTransfer.extensionality hM),
    ConstructionSaturationIndex.hartogs_semantics hM,ConstructionSaturationCardinals.cardinalsF_semantics hM,
    Project.Formula.satisfies_neg_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM),
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ForcingSupportSize.small_semantics (M := M),
    ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),ForcingProductFamily.presentation_semantics (M := M),
    ForcingLabelPermutations.carrier_semantics (M := M),ForcingSupportFilter.filter_semantics (M := M),
    ForcingSupportSize.injection_semantics (M := M),ForcingWithTopCarrier.empty_semantics (M := M),
    ForcingHS.hs_semantics (M := M),ForcingLabelSet.labelSet_semantics (M := M),ForcingAtomicRelations.forces_semantics (M := M),
    presentation_semantics hM,id_eq]
  exact ordinal_presentation hM hChoice env rho w mu I K B G F mul one mark top values c lo hi X x0 labels

/-- Original nativeZF proof kernel. The ALREADY COMPLETED internal L model
supplies the source ground Choice. No new interpretation or Choice assumption
is introduced; all original source mathematical guards remain explicit. -/
theorem kernel_certificate {k : Nat} (rho : Fin 7 → Fin k)
    (w mu I K B G F mul one mark top values c lo hi X x0 labels p : Fin k) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (ConstructibleGround.relative
      (sentence rho w mu I K B G F mul one mark top values c lo hi X x0 labels p))) := by
  apply ModelTransfer.derives
  intro N hN
  have hL := ConstructibleSource.model_zf hN
  have hRawChoice := (Project.FirstOrderSemantics.sentence_correct
    (ModelTransfer.extensionality hL) Axioms.choice).mp (ConstructibleSource.model_choice hN)
  obtain ⟨witness,_⟩ := ZF.exists_omega (ModelTransfer.project_models_iff.mp hL)
  let env : Env (Project.FirstOrderSemantics.reduct (ConstructibleSource.model hN)) 0 := ⟨Fin.elim0,fun _ => witness⟩
  have hSat : Project.Formula.satisfies env (ConstructionDirectedCardinality.choice (m := 0)) := by
    change Project.Formula.satisfies env (Axioms.choice.formula.rename Fin.elim0)
    rw [Project.Formula.satisfies_rename]
    exact hRawChoice env.free
  have hChoice := (ConstructionDirectedCardinality.choice_semantics hL env).mp hSat
  apply ConstructibleGround.relative_models hN
  exact (Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hL) _).mp
    (models rho w mu I K B G F mul one mark top values c lo hi X x0 labels p hL hChoice)

end PPAC.Migration.ForcingPresentationCover
