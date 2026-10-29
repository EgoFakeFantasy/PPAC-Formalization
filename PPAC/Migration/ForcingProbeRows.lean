/- Pinned CodeCardinals.ordinalType_lower_count: the SAME all-row relation R,
its total/single proofs and the actual ChainBound.cardinal_le_mul consumer. -/
import PPAC.Migration.ForcingProbeSingle
import PPAC.Migration.ForcingProbeRowHits
import PPAC.Migration.ForcingCohenChainBound

namespace PPAC.Migration.ForcingProbeRows
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ForcingProductSymmetry (orderFormula)
open ForcingSupportSize (MapsTo Injection)
open ForcingPrincipalFilter (EqF)
open ConstructionComponentCofinal (Chain)
open ConstructionComponentCarrier (Code)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def Witness {k : Nat} (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k)
    (I G F mul q bound labels E root w chain codes order ranks top r : Fin k)
    (A copies f beta i : M.Carrier .set) : Prop :=
  ∃ j index record d tau selected rankName nbeta,
    (Project.FirstOrderSemantics.reduct M).mem j A ∧
    PureKuratowski.Code M index i j ∧ PureKuratowski.PairMember M index record copies ∧
    PureKuratowski.Code M record d tau ∧ ForcingPowerName.Subset d f ∧
    (Project.FirstOrderSemantics.reduct M).mem selected (env codes) ∧
    PureKuratowski.PairMember M selected rankName (env ranks) ∧ ForcingCheckName.Checked (env top) beta nbeta ∧
    ForcingCodeSelection.IsSelected env rho I G F mul q bound labels E root w chain codes order selected f ∧
    ForcingCodeLinks.Links (orderFormula (rho 0) mul) env (env (rho 6)) (env w) (env (rho 0)) (env I) (env mul) (env q) (env chain) f (env root) tau selected ∧
    EqF (orderFormula (rho 0) mul) env (env (rho 6)) f (env r) rankName nbeta

def witness {k n : Nat} (rho : Fin 7 → Fin k)
    (I G F mul q bound labels E root w chain codes order ranks top r : Fin k)
    (base : Fin k → Fin n) (A copies f beta i : Fin n) : Project.Formula 1 n :=
  let up : Fin n → Fin (n+8) := fun j => j.succ.succ.succ.succ.succ.succ.succ.succ
  let rp : Fin k → Fin (n+8) := fun j => up (base j)
  (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.conj (.mem (.bound 7) (.bound (up A)))
    (.conj (ProjectSyntax.encode id (PairSyntax.ordered 6 (up i) 7))
    (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge (up copies) 6 5))
    (.conj (ProjectSyntax.encode id (PairSyntax.ordered 5 4 3))
    (.conj (Project.Formula.subset (.bound 4) (.bound (up f)))
    (.conj (.mem (.bound 2) (.bound (rp codes)))
    (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge (rp ranks) 2 1))
    (.conj (ProjectSyntax.encode id (ForcingCheckName.checkName (rp top) (up beta) 0))
    (.conj (ForcingCodeSelection.selected rho I G F mul q bound labels E root w chain codes order rp 2 (up f))
    (.conj (ForcingCodeLinks.links (orderFormula (rho 0) mul) rp (rp (rho 6)) (rp w) (rp (rho 0)) (rp I) (rp mul) (rp q) (rp chain) (up f) (rp root) 3 2)
    (ForcingPrincipalFilter.eqF (orderFormula (rho 0) mul) rp (rp (rho 6)) (up f) (rp r) 1 0)))))))))))))))))))

theorem witness_freeClosed {k n : Nat} (rho : Fin 7 → Fin k)
    (I G F mul q bound labels E root w chain codes order ranks top r : Fin k)
    (base : Fin k → Fin n) (A copies f beta i : Fin n) :
    (witness rho I G F mul q bound labels E root w chain codes order ranks top r base A copies f beta i).FreeClosed := by
  simp -implicitDefEqProofs [witness,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
    ForcingCodeSelection.selected_freeClosed,ForcingCodeLinks.links_freeClosed,ForcingPrincipalFilter.eqF_freeClosed]

theorem witness_semantics (hM : FirstOrder.Theory.Models M nativeZF) {k n : Nat}
    (env : Env (Project.FirstOrderSemantics.reduct M) n) (rho : Fin 7 → Fin k)
    (I G F mul q bound labels E root w chain codes order ranks top r : Fin k)
    (base : Fin k → Fin n) (A copies f beta i : Fin n) :
    Project.Formula.satisfies env (witness rho I G F mul q bound labels E root w chain codes order ranks top r base A copies f beta i) ↔
    Witness (fun j => env.bound (base j)) rho I G F mul q bound labels E root w chain codes order ranks top r
      (env.bound A) (env.bound copies) (env.bound f) (env.bound beta) (env.bound i) := by
  simp only [witness,Witness,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_mem_iff,Project.Formula.satisfies_subset_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_code,KuratowskiZF.source_edge,
    ForcingCheckName.checkName_semantics,ForcingCodeSelection.selected_semantics hM,
    ForcingCodeLinks.links_semantics hM,ForcingPrincipalFilter.eqF_semantics hM]
  rfl

theorem exists_relation (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k)
    (I G F mul q bound labels E root w chain codes order ranks top r : Fin k)
    (A copies theta : M.Carrier .set) :
    ∃ R, ∀ f beta i, ForcingChainBound.Values (KuratowskiZF.interpretation hM) R f beta i ↔
      (Project.FirstOrderSemantics.reduct M).mem f (env (rho 3)) ∧
      (Project.FirstOrderSemantics.reduct M).mem beta theta ∧ (Project.FirstOrderSemantics.reduct M).mem i A ∧
      Witness env rho I G F mul q bound labels E root w chain codes order ranks top r A copies f beta i := by
  have hZF := ModelTransfer.project_models_iff.mp hM
  let pair := KuratowskiZF.interpretation hM
  obtain ⟨Y,hY⟩ := ZF.exists_cartesianProduct hZF pair theta A
  obtain ⟨X,hX⟩ := ZF.exists_cartesianProduct hZF pair (env (rho 3)) Y
  let penv : Env (Project.FirstOrderSemantics.reduct M) (k+2) :=
    ⟨Fin.cases A (Fin.cases copies env),fun _ => theta⟩
  let schema : Project.UnarySchema (k+2) := {
    body := .existsE (.existsE (.existsE (.existsE
      (.conj (ProjectSyntax.encode id (PairSyntax.ordered 4 3 0))
        (.conj (ProjectSyntax.encode id (PairSyntax.ordered 0 2 1))
          (witness rho I G F mul q bound labels E root w chain codes order ranks top r
            (fun j => j.succ.succ.succ.succ.succ.succ.succ) 5 6 3 2 1))))))
    freeClosed := by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,witness_freeClosed] }
  have hs x : schema.denote penv x ↔ ∃ f beta i bi,
      PureKuratowski.Code M x f bi ∧ PureKuratowski.Code M bi beta i ∧
      Witness env rho I G F mul q bound labels E root w chain codes order ranks top r A copies f beta i := by
    simp only [schema,Project.UnarySchema.denote,Project.Formula.satisfies_exists_iff,
      Project.Formula.satisfies_conj_iff,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
      KuratowskiZF.source_code,witness_semantics hM]
    rfl
  obtain ⟨R,hR⟩ := ZF.separation_exists_d hZF schema penv X
  refine ⟨R,fun f beta i => ⟨?_,?_⟩⟩
  · rintro ⟨bi,hbi,x,hx,hxR⟩
    obtain ⟨hxX,hxs⟩ := (hR x).mp hxR
    obtain ⟨f',hf,bi',hbiY,hx'⟩ := (hX x).mp hxX
    obtain ⟨rfl,rfl⟩ := pair.injective hx hx'
    obtain ⟨beta',hb,i',hi,hbi'⟩ := (hY bi).mp hbiY
    obtain ⟨rfl,rfl⟩ := pair.injective hbi hbi'
    obtain ⟨f'',beta'',i'',bi'',hx'',hbi'',hWitness⟩ := (hs x).mp hxs
    obtain ⟨rfl,rfl⟩ := pair.injective hx hx''
    obtain ⟨rfl,rfl⟩ := pair.injective hbi hbi''
    exact ⟨hf,hb,hi,hWitness⟩
  · rintro ⟨hf,hb,hi,hWitness⟩
    obtain ⟨bi,hbi⟩ := pair.total beta i
    obtain ⟨x,hx⟩ := pair.total f bi
    exact ⟨bi,hbi,x,hx,(hR x).mpr ⟨(hX x).mpr ⟨f,hf,bi,(hY bi).mpr ⟨beta,hb,i,hi,hbi⟩,hx⟩,
      (hs x).mpr ⟨f,beta,i,bi,hx,hbi,hWitness⟩⟩⟩

theorem count_with_family (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M))
    {k : Nat}
    (env : Fin k → M.Carrier .set)
    (rho : Fin 7 → Fin k)
    (w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq r a U p e b t Ap Hp XP ordinal enum list J delta zero root vertices chain names Ar Hr codes order ranks selection group A P : Fin k)
    (targets copies multipliers : M.Carrier .set)
    (theta ntheta f : M.Carrier .set)
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega (env w))
    (hMu : (Project.FirstOrderSemantics.reduct M).IsInfiniteCardinal (KuratowskiZF.interpretation hM) (env w) (env mu))
    (hI : (Project.FirstOrderSemantics.reduct M).IsHartogsNumber (KuratowskiZF.interpretation hM) (env I) (env mu))
    (hSmall : ForcingSupportSize.Small (env (rho 0)) (env mu))
    (hMergers : ConstructionSaturationMergers.AllMergers (env w) (env history) (env kappa))
    (hRow : ConstructionTowerHistory.Row (env history) (env kappa) (env (rho 0)) (env mul) (env one) (env mark) (env H) (env C) (env incoming) (env base) (env kappa))
    (hm : ForcingDiagramPoset.LeftCancelMonoid (env (rho 0)) (env mul) (env one))
    (hp : ForcingProductFamily.Presentation (env (rho 0)) (env I) (env K) (env B) (env w) (env (rho 1)) (env (rho 2))
      (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hG : ForcingLabelPermutations.Carrier (env I) (env G))
    (hF : ForcingSupportFilter.Filter (env I) (env G) (env mu) (env F))
    (hLabelMap : ForcingConditionGraphs.FunctionOn (env K) (env labelMap))
    (hTop : ForcingWithTopCarrier.Empty (env top))
    (hLabels : ForcingLabelSet.LabelSet (env (rho 6)) (env I) (env K) (env labelMap) (env top) (env bit) (env labels))
    (hLabelBound : ForcingLabelBound.LabelBound (env (rho 6)) (env I) (env K) (env labelMap) (env top) (env bit) (env bound))
    (hq : Injection (env (rho 0)) (env I) (env q))
    (hAq : ForcingSupportedNames.Range (env (rho 0)) (env q) (env Aq))
    (hHq : ForcingLabelPermutations.Fixing (env G) (env Aq) (env Hq))
    (hE : ForcingSupportedNames.Supported (fun j => env (rho j)) (env Hq) (env E))
    (hrI : Injection (env (rho 0)) (env I) (env r))
    (hpI : Injection (env (rho 0)) (env I) (env p))
    (hAp : ForcingSupportedNames.Range (env (rho 0)) (env p) (env Ap))
    (hHp : ForcingLabelPermutations.Fixing (env G) (env Ap) (env Hp))
    (hXP : ForcingLocalNames.Carrier (fun j => env (rho j)) (env G) (env F) (env bound) (env Hp) (env XP))
    (ha : (Project.FirstOrderSemantics.reduct M).mem (env a) (env (rho 0)))
    (he : (Project.FirstOrderSemantics.reduct M).mem (env e) (env (rho 0)))
    (hb : (Project.FirstOrderSemantics.reduct M).mem (env b) (env (rho 0)))
    (hae : ForcingDiagramOrder.Product (env mul) (env a) (env e) (env t))
    (hSuba : ForcingDiagramOrder.Sub (env (rho 0)) (env mul) (env r) (env a) (env q))
    (hSubp : ForcingDiagramOrder.Sub (env (rho 0)) (env mul) (env r) (env t) (env p))
    (hEnum : (Project.FirstOrderSemantics.reduct M).IsSetBijectionFromTo (KuratowskiZF.interpretation hM) (env enum) (env ordinal) (env XP))
    (hList : ForcingCollectedName.Collected ForcingPowerName.trueTest Fin.elim0 (env ordinal) (env enum) (env (rho 6)) (env list))
    (hJ : ConstructionProbeSharedIntersections.ConditionalJoins (env (rho 0)) (env mul))
    (hzero : ForcingWithTopCarrier.Empty (env zero))
    (hNames : ForcingPowerName.Candidates (fun j => env (rho j)) (env G) (env F) (env bound) (env names))
    (hChain : Chain (env w) (env (rho 0)) (env I) (env mul) (env q) (env zero) (env root) (env vertices) (env chain))
    (hRoot : Code (env root) (env r) (env a) (env U))
    (hAr : ForcingSupportedNames.Range (env (rho 0)) (env r) (env Ar))
    (hHr : ForcingLabelPermutations.Fixing (env G) (env Ar) (env Hr))
    (hf : (Project.FirstOrderSemantics.reduct M).mem f (env (rho 3)))
    (hCarrier : ForcingTailCodes.Carrier (fun j => env (rho j)) (env G) (env F) (env bound) (env w) (env names) (env chain) (env codes))
    (hOrder : (Project.FirstOrderSemantics.reduct M).IsSetCodedWellOrder (KuratowskiZF.interpretation hM) (env order) (env codes))
    (hRanks : ForcingOrdinalRanks.Ranks
      (ForcingCohenSelection.liftRelation (ForcingCodeSelection.relation rho I G F mul q bound labels E root w chain codes order) id (rho 0) I (rho 2) w)
      env (env codes) (env order) (env (rho 6)) (env ranks))
    (hSelection : ForcingCollectedName.Collected
      (ForcingCohenSelection.liftRelation (ForcingCodeSelection.relation rho I G F mul q bound labels E root w chain codes order) id (rho 0) I (rho 2) w)
      env (env codes) (env ranks) (env (rho 6)) (env selection))
    (hFamily : ForcingOrdinalFixed.FixedFamily (fun j => env (rho j)) (env G) (env F) (env group) (env codes) (env ranks))
    (hIncl : ForcingPowerName.Subset (env Hr) (env group))
    (hChecked : ForcingCheckName.Checked (env top) theta ntheta)
    (hTheta : EqF (orderFormula (rho 0) mul) env (env (rho 6)) f (env r) (env selection) ntheta)
    (hTwo : ∃ o, (Project.FirstOrderSemantics.reduct M).IsOrdinalOne o ∧ (Project.FirstOrderSemantics.reduct M).SuccessorOf (env B) o)
    (hP : ForcingCohenCoordinates.Cartesian (env A) (env A) (env P))
    (hA : ¬ ForcingSupportSize.Small (env A) (env w))
    (hCopies : ForcingOutsideCopies.Family (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) env
      (fun j => env (rho j)) (env G) (env F) (env w) (env bound) (env labels) (env E) (env J) (env delta) (env list) (env P) targets copies)
    (hTargets : ForcingOutsideCopies.Targets (env (rho 0)) (env I) (env mul) (env r) (env b) (env p) (env P) multipliers targets)
    (hMultipliers : MapsTo (env P) (env (rho 0)) multipliers)
    (hProducts : ∀ i m, PureKuratowski.PairMember M i m multipliers → ForcingDiagramOrder.Product (env mul) m (env b) (env t))
    (hGeometry : ∀ i m, PureKuratowski.PairMember M i m multipliers → ForcingClassProfile.Geometry (env (rho 0)) (env mul) (env a) m (env t) (env U))
    (hIndependent : ∀ i j m n, PureKuratowski.PairMember M i m multipliers → PureKuratowski.PairMember M j n multipliers →
      i ≠ j → ConstructionDiagramPlacements.ConeEquality (env (rho 0)) (env mul) m n (env t))
    (hRangeJ : ForcingSupportedNames.Range (env (rho 0)) (env p) (env J))
    (hDelta : ForcingPowerName.Subset (env delta) f) :
    ∃ R Power nu W,
      (∀ g beta i, ForcingChainBound.Values (KuratowskiZF.interpretation hM) R g beta i ↔
        (Project.FirstOrderSemantics.reduct M).mem g (env (rho 3)) ∧
        (Project.FirstOrderSemantics.reduct M).mem beta theta ∧ (Project.FirstOrderSemantics.reduct M).mem i (env A) ∧
        Witness env rho I G F mul q bound labels E root w chain codes order ranks top r (env A) copies g beta i) ∧
      (Project.FirstOrderSemantics.reduct M).IsPowerSetOf Power (env w) ∧
      (Project.FirstOrderSemantics.reduct M).IsCardinalOf (KuratowskiZF.interpretation hM) nu Power ∧
      (Project.FirstOrderSemantics.reduct M).IsCartesianProduct (KuratowskiZF.interpretation hM) W theta nu ∧
      (Project.FirstOrderSemantics.reduct M).CardinalLessOrEqual (KuratowskiZF.interpretation hM) (env A) W := by
  obtain ⟨conditions,_,hProjection,hHits⟩ := ForcingProbeRowHits.source_construct hM hChoice env rho G F mul
    hw hp hP hA hCopies hTargets hrI hSubp hRangeJ hIndependent
  obtain ⟨R,hR⟩ := exists_relation hM env rho I G F mul q bound labels E root w chain codes order ranks top r
    (env A) copies theta
  have hTotal : ∀ i, (Project.FirstOrderSemantics.reduct M).mem i (env A) →
      ∃ beta, (Project.FirstOrderSemantics.reduct M).mem beta theta ∧
        ∃ g, (Project.FirstOrderSemantics.reduct M).mem g (env (rho 3)) ∧
          ForcingChainBound.Values (KuratowskiZF.interpretation hM) R g beta i := by
    intro i hi
    obtain ⟨f',j,d,hf',hff',hj,hValue,hdf'⟩ := hHits i hi f hf hDelta
    obtain ⟨index,hIndex,hCond⟩ := hValue
    obtain ⟨_,record,tau,hRecordEdge,hRecord⟩ := (hProjection index d).mp hCond
    obtain ⟨sm,hTarget,hCopy⟩ := hCopies.2 index record hRecordEdge
    obtain ⟨hsmI,_,m,hmEdge,hSubm⟩ := hTargets.2 index sm hTarget
    obtain ⟨z,hz⟩ := ForcingSupportingRoot.exists_code hM f' (env r)
    obtain ⟨g,beta,selected,rankName,nbeta,hg,_,hdg,_,hBeta,hSelected,hRank,hCheck,hSel,hLinks,hEq⟩ :=
      ForcingProbeTotal.witness_below hM hChoice env rho
        w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq r a U p e b t Ap Hp XP ordinal enum list J delta zero root vertices chain names Ar Hr codes order ranks selection group
        theta ntheta sm m record d tau f' z
        hw hMu hI hSmall hMergers hRow hm hp hG hF hLabelMap hTop hLabels hLabelBound hq hAq hHq hE
        hrI hpI hsmI hAp hHp hXP ha he (hMultipliers.2 index m hmEdge) hb hae (hProducts index m hmEdge)
        hSuba hSubm hSubp hEnum hList hCopy hRecord (hGeometry index m hmEdge)
        hJ hzero hNames hChain hRoot hAr hHr hf' hdf' hz hCarrier hOrder hRanks hSelection hFamily hIncl hChecked
        (ForcingPrincipalFilter.eqF_mono hM env rho mul hm hp hf' hrI hff' hTheta)
    exact ⟨beta,hBeta,g,hg,(hR g beta i).mpr ⟨hg,hBeta,hi,
      j,index,record,d,tau,selected,rankName,nbeta,hj,hIndex,hRecordEdge,hRecord,hdg,hSelected,hRank,hCheck,hSel,hLinks,hEq⟩⟩
  obtain ⟨Power,nu,compat,hPower,hNu,_,_,hC,hBound,hRefl⟩ := ForcingCohenChainBound.continuum hM
    (ConstructionDirectedCardinality.models_zfc hM hChoice) hw hTwo hp.2.1 hp.2.2.1
  have hSingle : ∀ beta i i' g g', (Project.FirstOrderSemantics.reduct M).mem beta theta →
      (Project.FirstOrderSemantics.reduct M).mem i (env A) → (Project.FirstOrderSemantics.reduct M).mem i' (env A) →
      (Project.FirstOrderSemantics.reduct M).mem g (env (rho 3)) → (Project.FirstOrderSemantics.reduct M).mem g' (env (rho 3)) →
      ForcingChainBound.Values (KuratowskiZF.interpretation hM) R g beta i →
      ForcingChainBound.Values (KuratowskiZF.interpretation hM) R g' beta i' →
      PureKuratowski.PairMember M g g' compat → i = i' := by
    intro beta i i' g g' _ _ _ hg hg' hv hv' hc
    apply Classical.byContradiction
    intro hne
    obtain ⟨_,_,_,j,index,record,d,tau,selected,rankName,nbeta,_,hIndex,hEdge,hRecord,hdg,hs,hrank,hcheck,hsel,hlinks,heq⟩ := (hR g beta i).mp hv
    obtain ⟨_,_,_,j',index',record',d',tau',selected',rankName',nbeta',_,hIndex',hEdge',hRecord',_,hs',hrank',hcheck',hsel',hlinks',heq'⟩ := (hR g' beta i').mp hv'
    obtain ⟨sm,hTarget,hCopy⟩ := hCopies.2 index record hEdge
    obtain ⟨sm',hTarget',hCopy'⟩ := hCopies.2 index' record' hEdge'
    obtain ⟨hsmI,hsmP,m,hmEdge,hSubm⟩ := hTargets.2 index sm hTarget
    obtain ⟨hsmI',hsmP',m',hmEdge',hSubm'⟩ := hTargets.2 index' sm' hTarget'
    have hindexne : index ≠ index' := by
      intro eq
      subst index'
      exact hne (PureKuratowski.code_injective hIndex hIndex').1
    have hNo := ForcingProbeSingle.incompatible_at hM hChoice env rho
      w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q zero root vertices chain names codes order ranks group r a U p t b Ap Hp XP ordinal enum list J delta
      sm sm' m m' record record' d tau d' tau' g g' selected selected' rankName rankName' beta nbeta nbeta'
      hw hMu hI hSmall hMergers hRow hm hp hG hF hLabelMap hTop hLabels hLabelBound hrI hpI hsmI hsmI'
      (hMultipliers.2 index m hmEdge) (hMultipliers.2 index' m' hmEdge') hb hSubm hSubm' hSubp hsmP hsmP'
      (hIndependent index index' m m' hmEdge hmEdge' hindexne) hAp hHp hXP hEnum hList hCopy hRecord hCopy' hRecord'
      hdg hChain hRoot hCarrier hOrder hRanks hFamily hs hs' hrank hrank' hsel hsel' hlinks hlinks' hcheck hcheck' heq heq'
    obtain ⟨c,hc,_,hgc,hg'c⟩ := ConstructionCohenCompatibility.exists_union hM hw
      ((hp.2.2.1 g).mp hg) ((hp.2.2.1 g').mp hg') ((hC g g').mp hc).2.2
    exact hNo ⟨c,(hp.2.2.1 c).mpr hc,hgc,hg'c⟩
  obtain ⟨W,hW⟩ := ZF.exists_cartesianProduct (ModelTransfer.project_models_iff.mp hM)
    (KuratowskiZF.interpretation hM) theta nu
  exact ⟨R,Power,nu,W,hR,hPower,hNu,hW,
    ForcingChainBound.cardinal_le_mul (KuratowskiZF.interpretation hM)
      (ConstructionDirectedCardinality.models_zfc hM hChoice) hRefl hBound hTotal hSingle hW⟩

theorem count_at (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M))
    {k : Nat}
    (env : Fin k → M.Carrier .set)
    (rho : Fin 7 → Fin k)
    (w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq r a U p e b t Ap Hp XP ordinal enum list J delta zero root vertices chain names Ar Hr codes order ranks selection group A P targets copies multipliers : Fin k)
    (theta ntheta f : M.Carrier .set)
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega (env w))
    (hMu : (Project.FirstOrderSemantics.reduct M).IsInfiniteCardinal (KuratowskiZF.interpretation hM) (env w) (env mu))
    (hI : (Project.FirstOrderSemantics.reduct M).IsHartogsNumber (KuratowskiZF.interpretation hM) (env I) (env mu))
    (hSmall : ForcingSupportSize.Small (env (rho 0)) (env mu))
    (hMergers : ConstructionSaturationMergers.AllMergers (env w) (env history) (env kappa))
    (hRow : ConstructionTowerHistory.Row (env history) (env kappa) (env (rho 0)) (env mul) (env one) (env mark) (env H) (env C) (env incoming) (env base) (env kappa))
    (hm : ForcingDiagramPoset.LeftCancelMonoid (env (rho 0)) (env mul) (env one))
    (hp : ForcingProductFamily.Presentation (env (rho 0)) (env I) (env K) (env B) (env w) (env (rho 1)) (env (rho 2))
      (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hG : ForcingLabelPermutations.Carrier (env I) (env G))
    (hF : ForcingSupportFilter.Filter (env I) (env G) (env mu) (env F))
    (hLabelMap : ForcingConditionGraphs.FunctionOn (env K) (env labelMap))
    (hTop : ForcingWithTopCarrier.Empty (env top))
    (hLabels : ForcingLabelSet.LabelSet (env (rho 6)) (env I) (env K) (env labelMap) (env top) (env bit) (env labels))
    (hLabelBound : ForcingLabelBound.LabelBound (env (rho 6)) (env I) (env K) (env labelMap) (env top) (env bit) (env bound))
    (hq : Injection (env (rho 0)) (env I) (env q))
    (hAq : ForcingSupportedNames.Range (env (rho 0)) (env q) (env Aq))
    (hHq : ForcingLabelPermutations.Fixing (env G) (env Aq) (env Hq))
    (hE : ForcingSupportedNames.Supported (fun j => env (rho j)) (env Hq) (env E))
    (hrI : Injection (env (rho 0)) (env I) (env r))
    (hpI : Injection (env (rho 0)) (env I) (env p))
    (hAp : ForcingSupportedNames.Range (env (rho 0)) (env p) (env Ap))
    (hHp : ForcingLabelPermutations.Fixing (env G) (env Ap) (env Hp))
    (hXP : ForcingLocalNames.Carrier (fun j => env (rho j)) (env G) (env F) (env bound) (env Hp) (env XP))
    (ha : (Project.FirstOrderSemantics.reduct M).mem (env a) (env (rho 0)))
    (he : (Project.FirstOrderSemantics.reduct M).mem (env e) (env (rho 0)))
    (hb : (Project.FirstOrderSemantics.reduct M).mem (env b) (env (rho 0)))
    (hae : ForcingDiagramOrder.Product (env mul) (env a) (env e) (env t))
    (hSuba : ForcingDiagramOrder.Sub (env (rho 0)) (env mul) (env r) (env a) (env q))
    (hSubp : ForcingDiagramOrder.Sub (env (rho 0)) (env mul) (env r) (env t) (env p))
    (hEnum : (Project.FirstOrderSemantics.reduct M).IsSetBijectionFromTo (KuratowskiZF.interpretation hM) (env enum) (env ordinal) (env XP))
    (hList : ForcingCollectedName.Collected ForcingPowerName.trueTest Fin.elim0 (env ordinal) (env enum) (env (rho 6)) (env list))
    (hJ : ConstructionProbeSharedIntersections.ConditionalJoins (env (rho 0)) (env mul))
    (hzero : ForcingWithTopCarrier.Empty (env zero))
    (hNames : ForcingPowerName.Candidates (fun j => env (rho j)) (env G) (env F) (env bound) (env names))
    (hChain : Chain (env w) (env (rho 0)) (env I) (env mul) (env q) (env zero) (env root) (env vertices) (env chain))
    (hRoot : Code (env root) (env r) (env a) (env U))
    (hAr : ForcingSupportedNames.Range (env (rho 0)) (env r) (env Ar))
    (hHr : ForcingLabelPermutations.Fixing (env G) (env Ar) (env Hr))
    (hf : (Project.FirstOrderSemantics.reduct M).mem f (env (rho 3)))
    (hCarrier : ForcingTailCodes.Carrier (fun j => env (rho j)) (env G) (env F) (env bound) (env w) (env names) (env chain) (env codes))
    (hOrder : (Project.FirstOrderSemantics.reduct M).IsSetCodedWellOrder (KuratowskiZF.interpretation hM) (env order) (env codes))
    (hRanks : ForcingOrdinalRanks.Ranks
      (ForcingCohenSelection.liftRelation (ForcingCodeSelection.relation rho I G F mul q bound labels E root w chain codes order) id (rho 0) I (rho 2) w)
      env (env codes) (env order) (env (rho 6)) (env ranks))
    (hSelection : ForcingCollectedName.Collected
      (ForcingCohenSelection.liftRelation (ForcingCodeSelection.relation rho I G F mul q bound labels E root w chain codes order) id (rho 0) I (rho 2) w)
      env (env codes) (env ranks) (env (rho 6)) (env selection))
    (hFamily : ForcingOrdinalFixed.FixedFamily (fun j => env (rho j)) (env G) (env F) (env group) (env codes) (env ranks))
    (hIncl : ForcingPowerName.Subset (env Hr) (env group))
    (hChecked : ForcingCheckName.Checked (env top) theta ntheta)
    (hTheta : EqF (orderFormula (rho 0) mul) env (env (rho 6)) f (env r) (env selection) ntheta)
    (hTwo : ∃ o, (Project.FirstOrderSemantics.reduct M).IsOrdinalOne o ∧ (Project.FirstOrderSemantics.reduct M).SuccessorOf (env B) o)
    (hP : ForcingCohenCoordinates.Cartesian (env A) (env A) (env P))
    (hA : ¬ ForcingSupportSize.Small (env A) (env w))
    (hCopies : ForcingOutsideCopies.Family (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) env
      (fun j => env (rho j)) (env G) (env F) (env w) (env bound) (env labels) (env E) (env J) (env delta) (env list) (env P) (env targets) (env copies))
    (hTargets : ForcingOutsideCopies.Targets (env (rho 0)) (env I) (env mul) (env r) (env b) (env p) (env P) (env multipliers) (env targets))
    (hMultipliers : MapsTo (env P) (env (rho 0)) (env multipliers))
    (hProducts : ∀ i m, PureKuratowski.PairMember M i m (env multipliers) → ForcingDiagramOrder.Product (env mul) m (env b) (env t))
    (hGeometry : ∀ i m, PureKuratowski.PairMember M i m (env multipliers) → ForcingClassProfile.Geometry (env (rho 0)) (env mul) (env a) m (env t) (env U))
    (hIndependent : ∀ i j m n, PureKuratowski.PairMember M i m (env multipliers) → PureKuratowski.PairMember M j n (env multipliers) →
      i ≠ j → ConstructionDiagramPlacements.ConeEquality (env (rho 0)) (env mul) m n (env t))
    (hRangeJ : ForcingSupportedNames.Range (env (rho 0)) (env p) (env J))
    (hDelta : ForcingPowerName.Subset (env delta) f) :
    ∃ R Power nu W,
      (∀ g beta i, ForcingChainBound.Values (KuratowskiZF.interpretation hM) R g beta i ↔
        (Project.FirstOrderSemantics.reduct M).mem g (env (rho 3)) ∧
        (Project.FirstOrderSemantics.reduct M).mem beta theta ∧ (Project.FirstOrderSemantics.reduct M).mem i (env A) ∧
        Witness env rho I G F mul q bound labels E root w chain codes order ranks top r (env A) (env copies) g beta i) ∧
      (Project.FirstOrderSemantics.reduct M).IsPowerSetOf Power (env w) ∧
      (Project.FirstOrderSemantics.reduct M).IsCardinalOf (KuratowskiZF.interpretation hM) nu Power ∧
      (Project.FirstOrderSemantics.reduct M).IsCartesianProduct (KuratowskiZF.interpretation hM) W theta nu ∧
      (Project.FirstOrderSemantics.reduct M).CardinalLessOrEqual (KuratowskiZF.interpretation hM) (env A) W := by
  exact count_with_family hM hChoice env rho w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq r a U p e b t Ap Hp XP ordinal enum list J delta zero root vertices chain names Ar Hr codes order ranks selection group A P (env targets) (env copies) (env multipliers) theta ntheta f hw hMu hI hSmall hMergers hRow hm hp hG hF hLabelMap hTop hLabels hLabelBound hq hAq hHq hE hrI hpI hAp hHp hXP ha he hb hae hSuba hSubp hEnum hList hJ hzero hNames hChain hRoot hAr hHr hf hCarrier hOrder hRanks hSelection hFamily hIncl hChecked hTheta hTwo hP hA hCopies hTargets hMultipliers hProducts hGeometry hIndependent hRangeJ hDelta

theorem source_construct (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M))
    {k : Nat}
    (env : Fin k → M.Carrier .set)
    (rho : Fin 7 → Fin k)
    (w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq r a U p e b t Ap Hp XP ordinal enum list J delta zero root vertices chain names Ar Hr codes order ranks selection group theta ntheta f A P targets copies multipliers : Fin k)
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega (env w))
    (hMu : (Project.FirstOrderSemantics.reduct M).IsInfiniteCardinal (KuratowskiZF.interpretation hM) (env w) (env mu))
    (hI : (Project.FirstOrderSemantics.reduct M).IsHartogsNumber (KuratowskiZF.interpretation hM) (env I) (env mu))
    (hSmall : ForcingSupportSize.Small (env (rho 0)) (env mu))
    (hMergers : ConstructionSaturationMergers.AllMergers (env w) (env history) (env kappa))
    (hRow : ConstructionTowerHistory.Row (env history) (env kappa) (env (rho 0)) (env mul) (env one) (env mark) (env H) (env C) (env incoming) (env base) (env kappa))
    (hm : ForcingDiagramPoset.LeftCancelMonoid (env (rho 0)) (env mul) (env one))
    (hp : ForcingProductFamily.Presentation (env (rho 0)) (env I) (env K) (env B) (env w) (env (rho 1)) (env (rho 2))
      (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hG : ForcingLabelPermutations.Carrier (env I) (env G))
    (hF : ForcingSupportFilter.Filter (env I) (env G) (env mu) (env F))
    (hLabelMap : ForcingConditionGraphs.FunctionOn (env K) (env labelMap))
    (hTop : ForcingWithTopCarrier.Empty (env top))
    (hLabels : ForcingLabelSet.LabelSet (env (rho 6)) (env I) (env K) (env labelMap) (env top) (env bit) (env labels))
    (hLabelBound : ForcingLabelBound.LabelBound (env (rho 6)) (env I) (env K) (env labelMap) (env top) (env bit) (env bound))
    (hq : Injection (env (rho 0)) (env I) (env q))
    (hAq : ForcingSupportedNames.Range (env (rho 0)) (env q) (env Aq))
    (hHq : ForcingLabelPermutations.Fixing (env G) (env Aq) (env Hq))
    (hE : ForcingSupportedNames.Supported (fun j => env (rho j)) (env Hq) (env E))
    (hrI : Injection (env (rho 0)) (env I) (env r))
    (hpI : Injection (env (rho 0)) (env I) (env p))
    (hAp : ForcingSupportedNames.Range (env (rho 0)) (env p) (env Ap))
    (hHp : ForcingLabelPermutations.Fixing (env G) (env Ap) (env Hp))
    (hXP : ForcingLocalNames.Carrier (fun j => env (rho j)) (env G) (env F) (env bound) (env Hp) (env XP))
    (ha : (Project.FirstOrderSemantics.reduct M).mem (env a) (env (rho 0)))
    (he : (Project.FirstOrderSemantics.reduct M).mem (env e) (env (rho 0)))
    (hb : (Project.FirstOrderSemantics.reduct M).mem (env b) (env (rho 0)))
    (hae : ForcingDiagramOrder.Product (env mul) (env a) (env e) (env t))
    (hSuba : ForcingDiagramOrder.Sub (env (rho 0)) (env mul) (env r) (env a) (env q))
    (hSubp : ForcingDiagramOrder.Sub (env (rho 0)) (env mul) (env r) (env t) (env p))
    (hEnum : (Project.FirstOrderSemantics.reduct M).IsSetBijectionFromTo (KuratowskiZF.interpretation hM) (env enum) (env ordinal) (env XP))
    (hList : ForcingCollectedName.Collected ForcingPowerName.trueTest Fin.elim0 (env ordinal) (env enum) (env (rho 6)) (env list))
    (hJ : ConstructionProbeSharedIntersections.ConditionalJoins (env (rho 0)) (env mul))
    (hzero : ForcingWithTopCarrier.Empty (env zero))
    (hNames : ForcingPowerName.Candidates (fun j => env (rho j)) (env G) (env F) (env bound) (env names))
    (hChain : Chain (env w) (env (rho 0)) (env I) (env mul) (env q) (env zero) (env root) (env vertices) (env chain))
    (hRoot : Code (env root) (env r) (env a) (env U))
    (hAr : ForcingSupportedNames.Range (env (rho 0)) (env r) (env Ar))
    (hHr : ForcingLabelPermutations.Fixing (env G) (env Ar) (env Hr))
    (hf : (Project.FirstOrderSemantics.reduct M).mem (env f) (env (rho 3)))
    (hCarrier : ForcingTailCodes.Carrier (fun j => env (rho j)) (env G) (env F) (env bound) (env w) (env names) (env chain) (env codes))
    (hOrder : (Project.FirstOrderSemantics.reduct M).IsSetCodedWellOrder (KuratowskiZF.interpretation hM) (env order) (env codes))
    (hRanks : ForcingOrdinalRanks.Ranks
      (ForcingCohenSelection.liftRelation (ForcingCodeSelection.relation rho I G F mul q bound labels E root w chain codes order) id (rho 0) I (rho 2) w)
      env (env codes) (env order) (env (rho 6)) (env ranks))
    (hSelection : ForcingCollectedName.Collected
      (ForcingCohenSelection.liftRelation (ForcingCodeSelection.relation rho I G F mul q bound labels E root w chain codes order) id (rho 0) I (rho 2) w)
      env (env codes) (env ranks) (env (rho 6)) (env selection))
    (hFamily : ForcingOrdinalFixed.FixedFamily (fun j => env (rho j)) (env G) (env F) (env group) (env codes) (env ranks))
    (hIncl : ForcingPowerName.Subset (env Hr) (env group))
    (hChecked : ForcingCheckName.Checked (env top) (env theta) (env ntheta))
    (hTheta : EqF (orderFormula (rho 0) mul) env (env (rho 6)) (env f) (env r) (env selection) (env ntheta))
    (hTwo : ∃ o, (Project.FirstOrderSemantics.reduct M).IsOrdinalOne o ∧ (Project.FirstOrderSemantics.reduct M).SuccessorOf (env B) o)
    (hP : ForcingCohenCoordinates.Cartesian (env A) (env A) (env P))
    (hA : ¬ ForcingSupportSize.Small (env A) (env w))
    (hCopies : ForcingOutsideCopies.Family (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) env
      (fun j => env (rho j)) (env G) (env F) (env w) (env bound) (env labels) (env E) (env J) (env delta) (env list) (env P) (env targets) (env copies))
    (hTargets : ForcingOutsideCopies.Targets (env (rho 0)) (env I) (env mul) (env r) (env b) (env p) (env P) (env multipliers) (env targets))
    (hMultipliers : MapsTo (env P) (env (rho 0)) (env multipliers))
    (hProducts : ∀ i m, PureKuratowski.PairMember M i m (env multipliers) → ForcingDiagramOrder.Product (env mul) m (env b) (env t))
    (hGeometry : ∀ i m, PureKuratowski.PairMember M i m (env multipliers) → ForcingClassProfile.Geometry (env (rho 0)) (env mul) (env a) m (env t) (env U))
    (hIndependent : ∀ i j m n, PureKuratowski.PairMember M i m (env multipliers) → PureKuratowski.PairMember M j n (env multipliers) →
      i ≠ j → ConstructionDiagramPlacements.ConeEquality (env (rho 0)) (env mul) m n (env t))
    (hRangeJ : ForcingSupportedNames.Range (env (rho 0)) (env p) (env J))
    (hDelta : ForcingPowerName.Subset (env delta) (env f)) :
    ∃ R Power nu W,
      (∀ g beta i, ForcingChainBound.Values (KuratowskiZF.interpretation hM) R g beta i ↔
        (Project.FirstOrderSemantics.reduct M).mem g (env (rho 3)) ∧
        (Project.FirstOrderSemantics.reduct M).mem beta (env theta) ∧ (Project.FirstOrderSemantics.reduct M).mem i (env A) ∧
        Witness env rho I G F mul q bound labels E root w chain codes order ranks top r (env A) (env copies) g beta i) ∧
      (Project.FirstOrderSemantics.reduct M).IsPowerSetOf Power (env w) ∧
      (Project.FirstOrderSemantics.reduct M).IsCardinalOf (KuratowskiZF.interpretation hM) nu Power ∧
      (Project.FirstOrderSemantics.reduct M).IsCartesianProduct (KuratowskiZF.interpretation hM) W (env theta) nu ∧
      (Project.FirstOrderSemantics.reduct M).CardinalLessOrEqual (KuratowskiZF.interpretation hM) (env A) W := by
  exact count_at hM hChoice env rho w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq r a U p e b t Ap Hp XP ordinal enum list J delta zero root vertices chain names Ar Hr codes order ranks selection group A P targets copies multipliers (env theta) (env ntheta) (env f) hw hMu hI hSmall hMergers hRow hm hp hG hF hLabelMap hTop hLabels hLabelBound hq hAq hHq hE hrI hpI hAp hHp hXP ha he hb hae hSuba hSubp hEnum hList hJ hzero hNames hChain hRoot hAr hHr hf hCarrier hOrder hRanks hSelection hFamily hIncl hChecked hTheta hTwo hP hA hCopies hTargets hMultipliers hProducts hGeometry hIndependent hRangeJ hDelta

def sourceSentence {k : Nat} (rho : Fin 7 → Fin k) (w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq r a U p e b t Ap Hp XP ordinal enum list J delta zero root vertices chain names Ar Hr codes order ranks selection group theta ntheta f A P targets copies multipliers : Fin k) : Project.Sentence where
  formula :=
    let up : Fin k → Fin (k+4) := fun j => j.succ.succ.succ.succ
    let R := ForcingCodeSelection.relation rho I G F mul q bound labels E root w chain codes order
    let L := ForcingCohenSelection.liftRelation R id (rho 0) I (rho 2) w
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
    (.imp (ProjectSyntax.encode id (ForcingLabelBound.labelBound (rho 6) I K labelMap top bit bound))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.injection q (rho 0) I))
    (.imp (ProjectSyntax.encode id (ForcingSupportedNames.range (rho 0) q Aq))
    (.imp (ProjectSyntax.encode id (ForcingLabelPermutations.fixing G Aq Hq))
    (.imp (ProjectSyntax.encode id (ForcingEquivariantMix.fixedAll rho Hq E))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.injection r (rho 0) I))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.injection p (rho 0) I))
    (.imp (ProjectSyntax.encode id (ForcingSupportedNames.range (rho 0) p Ap))
    (.imp (ProjectSyntax.encode id (ForcingLabelPermutations.fixing G Ap Hp))
    (.imp (ProjectSyntax.encode id (ForcingLocalNames.carrier rho G F bound Hp XP))
    (.imp (.mem (.bound a) (.bound (rho 0)))
    (.imp (.mem (.bound e) (.bound (rho 0)))
    (.imp (.mem (.bound b) (.bound (rho 0)))
    (.imp (ProjectSyntax.encode id (ForcingDiagramOrder.product mul a e t))
    (.imp (ProjectSyntax.encode id (ForcingDiagramOrder.sub (rho 0) mul r a q))
    (.imp (ProjectSyntax.encode id (ForcingDiagramOrder.sub (rho 0) mul r t p))
    (.imp (Project.Formula.isBijectionFromTo PureKuratowskiProject.convention (.bound enum) (.bound ordinal) (.bound XP))
    (.imp (ProjectSyntax.encode id (ForcingCollectedName.collected ForcingPowerName.trueTest Fin.elim0 ordinal enum (rho 6) list))
    (.imp (ConstructionProbeSharedIntersections.conditionalJoins (rho 0) mul)
    (.imp (ProjectSyntax.encode id (ForcingWithTopCarrier.empty zero))
    (.imp (ForcingTailCodes.candidates rho G F bound names)
    (.imp (ConstructionComponentCofinal.chain w (rho 0) I mul q zero root vertices chain)
    (.imp (ConstructionComponentCarrier.code root r a U)
    (.imp (ProjectSyntax.encode id (ForcingSupportedNames.range (rho 0) r Ar))
    (.imp (ProjectSyntax.encode id (ForcingLabelPermutations.fixing G Ar Hr))
    (.imp (.mem (.bound f) (.bound (rho 3)))
    (.imp (ForcingTailCodes.carrier rho G F bound w names chain codes)
    (.imp (Project.Formula.isSetCodedWellOrder PureKuratowskiProject.convention (.bound order) (.bound codes))
    (.imp (ProjectSyntax.encode id (ForcingOrdinalRanks.ranks L id codes order (rho 6) ranks))
    (.imp (ProjectSyntax.encode id (ForcingCollectedName.collected L id codes ranks (rho 6) selection))
    (.imp (ProjectSyntax.encode id (ForcingOrdinalFixed.fixedFamily rho G F group codes ranks))
    (.imp (Project.Formula.subset (.bound Hr) (.bound group))
    (.imp (ProjectSyntax.encode id (ForcingCheckName.checkName top theta ntheta))
    (.imp (ForcingPrincipalFilter.eqF (orderFormula (rho 0) mul) id (rho 6) f r selection ntheta)
    (.imp (ForcingProductParameters.two B)
    (.imp (ProjectSyntax.encode id (ForcingCohenCoordinates.cartesian A A P))
    (.imp (.neg (ProjectSyntax.encode id (ForcingSupportSize.small A w)))
    (.imp (ForcingOutsideCopies.family (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) id rho G F w bound labels E J delta list P targets copies)
    (.imp (ForcingOutsideCopies.targets (rho 0) I mul r b p P multipliers targets)
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.mapsTo multipliers P (rho 0)))
    (.imp (.forallE (.forallE (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge multipliers.succ.succ 1 0)) (ProjectSyntax.encode id (ForcingDiagramOrder.product mul.succ.succ 0 b.succ.succ t.succ.succ)))))
    (.imp (.forallE (.forallE (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge multipliers.succ.succ 1 0)) (ForcingClassProfile.geometry (rho 0).succ.succ mul.succ.succ a.succ.succ 0 t.succ.succ U.succ.succ))))
    (.imp (ForcingProbeRowHits.independent (rho 0) mul t multipliers)
    (.imp (ProjectSyntax.encode id (ForcingSupportedNames.range (rho 0) p J))
    (.imp (Project.Formula.subset (.bound delta) (.bound f))
    (.existsE (.existsE (.existsE (.existsE
      (.conj (.forallE (.forallE (.forallE
        (.iff (ForcingChainBound.rel (𝒞 := PureKuratowskiProject.convention) (.bound 6) (.bound 2) (.bound 1) (.bound 0))
          (.conj (.mem (.bound 2) (.bound ((up (rho 3)).succ.succ.succ)))
          (.conj (.mem (.bound 1) (.bound ((up theta).succ.succ.succ)))
          (.conj (.mem (.bound 0) (.bound ((up A).succ.succ.succ)))
            (witness rho I G F mul q bound labels E root w chain codes order ranks top r
              (fun j => (up j).succ.succ.succ) (up A).succ.succ.succ (up copies).succ.succ.succ 2 1 0))))))))
      (.conj (Project.Formula.isPowerSet (.bound 2) (.bound (up w)))
      (.conj (Project.Formula.isCardinalOf PureKuratowskiProject.convention (.bound 1) (.bound 2))
      (.conj (Project.Formula.isCartesianProduct PureKuratowskiProject.convention (.bound 0) (.bound (up theta)) (.bound 1))
        (Project.Formula.cardinalLessOrEqual PureKuratowskiProject.convention (.bound (up A)) (.bound 0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
      ConstructionSaturationIndex.hartogs_freeClosed,ConstructionSaturationMergers.allMergers_freeClosed,
      ConstructionTowerHistory.row_freeClosed,ConstructionProbeSharedIntersections.conditionalJoins_freeClosed,
      ForcingTailCodes.candidates_freeClosed,ConstructionComponentCofinal.chain_freeClosed,
      ConstructionComponentCarrier.code_freeClosed,ForcingPrincipalFilter.eqF_freeClosed,
      ForcingClassProfile.geometry_freeClosed,
      ForcingTailCodes.carrier_freeClosed,Project.Formula.isSetCodedWellOrder_freeClosed,
      
      ForcingOutsideCopies.family_freeClosed,ForcingOutsideCopies.targets_freeClosed,
      ForcingProbeRowHits.independent_freeClosed,ForcingProductParameters.two_freeClosed,
      ForcingChainBound.rel_freeClosed,witness_freeClosed]

theorem source_models {k : Nat} (rho : Fin 7 → Fin k) (w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq r a U p e b t Ap Hp XP ordinal enum list J delta zero root vertices chain names Ar Hr codes order ranks selection group theta ntheta f A P targets copies multipliers : Fin k)
    (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) :
    (Project.fo_sentence (sourceSentence rho w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq r a U p e b t Ap Hp XP ordinal enum list J delta zero root vertices chain names Ar Hr codes order ranks selection group theta ntheta f A P targets copies multipliers)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM),SetTheory.Structure.satisfiesSentence_iff]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro env
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    Project.Formula.satisfies_subset_iff,
    Project.Formula.satisfies_isOmega_iff,
    Project.Formula.satisfies_isInfiniteCardinal_iff (KuratowskiZF.interpretation hM) (ModelTransfer.extensionality hM),
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ConstructionSaturationIndex.hartogs_semantics hM,
    ConstructionSaturationMergers.allMergers_semantics hM,ConstructionTowerHistory.row_semantics hM,
    ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),ConstructionProbeSharedIntersections.conditionalJoins_semantics hM,
    ForcingProductFamily.presentation_semantics (M := M),ForcingLabelPermutations.carrier_semantics (M := M),
    ForcingSupportFilter.filter_semantics (M := M),ForcingConditionGraphs.functionOn_semantics (M := M),
    ForcingWithTopCarrier.empty_semantics (M := M),ForcingLabelSet.labelSet_semantics (M := M),
    ForcingLabelBound.labelBound_semantics (M := M),ForcingSupportSize.injection_semantics (M := M),
    ForcingSupportedNames.range_semantics (M := M),ForcingLabelPermutations.fixing_semantics (M := M),
    ForcingSupportedNames.supported_semantics (M := M),ForcingTailCodes.candidates_semantics hM,
    ConstructionComponentCofinal.chain_semantics hM,ConstructionComponentCarrier.code_semantics hM,
    
    KuratowskiZF.source_edge,ForcingPrincipalFilter.eqF_semantics hM,
    ForcingLocalNames.carrier_semantics (M := M),ForcingDiagramOrder.product_semantics (M := M),ForcingDiagramOrder.sub_semantics (M := M),
    Project.Formula.satisfies_isBijectionFromTo_iff (KuratowskiZF.interpretation hM) (ModelTransfer.extensionality hM),
    ForcingCollectedName.collected_semantics (M := M),
    ForcingClassProfile.geometry_semantics hM,
    ForcingTailCodes.carrier_semantics hM,Project.Formula.satisfies_isSetCodedWellOrder_iff (KuratowskiZF.interpretation hM),
    ForcingOrdinalRanks.ranks_semantics (M := M),ForcingOrdinalFixed.fixedFamily_semantics (M := M),
    ForcingCheckName.checkName_semantics (M := M),
    
    Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_iff_iff,Project.Formula.satisfies_neg_iff,
    ForcingOutsideCopies.family_semantics hM,ForcingOutsideCopies.targets_semantics hM,
    ForcingCohenCoordinates.cartesian_semantics (M := M),ForcingSupportSize.small_semantics (M := M),
    ForcingSupportSize.mapsTo_semantics (M := M),ForcingProbeRowHits.independent_semantics hM,
    ForcingProductParameters.two_semantics (M := M),ForcingChainBound.rel_semantics (KuratowskiZF.interpretation hM),
    witness_semantics hM,Project.Formula.satisfies_isPowerSet_iff,
    Project.Formula.satisfies_isCardinalOf_iff (KuratowskiZF.interpretation hM) (ModelTransfer.extensionality hM),
    Project.Formula.satisfies_isCartesianProduct_iff (KuratowskiZF.interpretation hM),
    Project.Formula.satisfies_cardinalLessOrEqual_iff (KuratowskiZF.interpretation hM) (ModelTransfer.extensionality hM)]
  exact source_construct hM hChoice env rho w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq r a U p e b t Ap Hp XP ordinal enum list J delta zero root vertices chain names Ar Hr codes order ranks selection group theta ntheta f A P targets copies multipliers

theorem source_kernel_certificate {k : Nat} (rho : Fin 7 → Fin k) (w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq r a U p e b t Ap Hp XP ordinal enum list J delta zero root vertices chain names Ar Hr codes order ranks selection group theta ntheta f A P targets copies multipliers : Fin k) :
    FirstOrder.Derives nativeZF []
      (Project.fo_sentence (ConstructibleGround.relative (sourceSentence rho w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq r a U p e b t Ap Hp XP ordinal enum list J delta zero root vertices chain names Ar Hr codes order ranks selection group theta ntheta f A P targets copies multipliers))) := by
  apply ModelTransfer.derives
  intro M hM
  have hL := ConstructibleSource.model_zf hM
  have hRawChoice := (Project.FirstOrderSemantics.sentence_correct
    (ModelTransfer.extensionality hL) Axioms.choice).mp (ConstructibleSource.model_choice hM)
  let witness := Classical.choice ((ConstructibleSource.model hM).nonempty .set)
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct (ConstructibleSource.model hM)) 0 :=
    {bound := Fin.elim0,free := fun _ => witness}
  have hSat : Project.Formula.satisfies env (ConstructionDirectedCardinality.choice (m := 0)) := by
    change Project.Formula.satisfies env (Axioms.choice.formula.rename Fin.elim0)
    rw [Project.Formula.satisfies_rename]
    exact hRawChoice env.free
  have hChoice := (ConstructionDirectedCardinality.choice_semantics hL env).mp hSat
  apply ConstructibleGround.relative_models hM (sourceSentence rho w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq r a U p e b t Ap Hp XP ordinal enum list J delta zero root vertices chain names Ar Hr codes order ranks selection group theta ntheta f A P targets copies multipliers)
  exact (Project.FirstOrderSemantics.sentence_correct
    (ModelTransfer.extensionality hL) (sourceSentence rho w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq r a U p e b t Ap Hp XP ordinal enum list J delta zero root vertices chain names Ar Hr codes order ranks selection group theta ntheta f A P targets copies multipliers)).mp
      (source_models rho w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq r a U p e b t Ap Hp XP ordinal enum list J delta zero root vertices chain names Ar Hr codes order ranks selection group theta ntheta f A P targets copies multipliers hL hChoice)

end PPAC.Migration.ForcingProbeRows
