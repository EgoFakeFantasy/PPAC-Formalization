/- Pinned UniformImages.uniform_maximum_dense:291-335. Reuse the existing
common-root preparation, localized_maximum, native Collection and donor
uniformization. Actual internal family, not an external choice function. -/
import PPAC.Migration.ForcingActualOrdinalChoice

namespace PPAC.Migration.ForcingUniformMaximum
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open Source (Formula)
open Source.SetLanguage (args1 args2 args3)
open ForcingFormula (Force)
open ForcingAtomicRelations (Forces)
open ForcingMapConditions (MapRel)
open ForcingProductFamily (Presentation actionFormula mapRel_action)
open ForcingProductSymmetry (orderFormula orderFormula_semantics)
open ForcingPairUnion (domain domain_semantics)
open ForcingSupportSize (Injection Small)
open ForcingSupportedNames (Supported Range)
open ForcingCheckName (Checked)
open ForcingSupportingRoot (Code)
open ForcingCohenConditions (Condition)
open ForcingConditionGraphs (FunctionOn)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1800000
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

/-- Source uniform_maximum_dense roots. The same q and zq are prepared
BEFORE any family member or maximum witness is selected. -/
def Prepared {k : Nat} (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k)
    (I G F mul w mark : Fin k) (S start d p q Jp Hp Jq Hq zp zq : M.Carrier .set) : Prop :=
  Condition (env (rho 2)) (env w) d ∧ Injection (env (rho 0)) (env I) p ∧ Injection (env (rho 0)) (env I) q ∧
  ForcingDiagramOrder.Sub (env (rho 0)) (env mul) q (env mark) p ∧
  Range (env (rho 0)) p Jp ∧ ForcingLabelPermutations.Fixing (env G) Jp Hp ∧
  Range (env (rho 0)) q Jq ∧ ForcingLabelPermutations.Fixing (env G) Jq Hq ∧
  (∀ pi, (Project.FirstOrderSemantics.reduct M).mem pi Hp → (Project.FirstOrderSemantics.reduct M).mem pi S) ∧
  ForcingLocalRecordPullback.Supported (env (rho 0)) q d ∧ Code zp d p ∧ Code zq d q ∧
  (Project.FirstOrderSemantics.reduct M).mem zp (env (rho 6)) ∧
  (Project.FirstOrderSemantics.reduct M).mem zq (env (rho 6)) ∧
  MapRel (orderFormula (rho 0) mul) env zp start ∧ MapRel (orderFormula (rho 0) mul) env zq start ∧
  ForcingConjugationGraph.Subgroup (env I) (env G) Hq ∧ (Project.FirstOrderSemantics.reduct M).mem Hq (env F)

/-- The EXISTING source support/condition preparation, independent of every
family index, parameter vector, formula and selected witness. -/
theorem prepare (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k)
    (w mu unit mark I K B G F mul : Fin k) {S start : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega (env w))
    (hMu : (Project.FirstOrderSemantics.reduct M).IsInfiniteCardinal (KuratowskiZF.interpretation hM) (env w) (env mu))
    (hI : (Project.FirstOrderSemantics.reduct M).IsHartogsNumber (KuratowskiZF.interpretation hM) (env I) (env mu))
    (hD : Small (env (rho 0)) (env mu))
    (hCard : ConstructionSaturationCardinals.Cardinals hM (env (rho 0)) (env mul) (env mark) (env mu))
    (hm : ForcingDiagramPoset.LeftCancelMonoid (env (rho 0)) (env mul) (env unit))
    (hPres : Presentation (env (rho 0)) (env I) (env K) (env B) (env w)
      (env (rho 1)) (env (rho 2)) (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hG : ForcingLabelPermutations.Carrier (env I) (env G))
    (hFilter : ForcingSupportFilter.Filter (env I) (env G) (env mu) (env F))
    (hMark : (Project.FirstOrderSemantics.reduct M).mem (env mark) (env (rho 0)))
    (hSF : (Project.FirstOrderSemantics.reduct M).mem S (env F))
    (hStart : (Project.FirstOrderSemantics.reduct M).mem start (env (rho 6))) :
    ∃ d p q Jp Hp Jq Hq zp zq, Prepared env rho I G F mul w mark S start d p q Jp Hp Jq Hq zp zq := by
  have hZF := ModelTransfer.project_models_iff.mp hM
  let pair := KuratowskiZF.interpretation hM
  let R := orderFormula (rho 0) mul
  let W := env (rho 6)
  have hpre := ForcingProductPoset.preorder env (rho 0) mul (rho 6) hm
    hPres.2.2.2.2.1 hPres.2.2.2.1 hPres.2.2.2.2.2
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
  obtain ⟨d,s,z,hDcond,hS,hZ,hZStart⟩ := ForcingLabelDensity.exists_condition_below hM hPres hm hRoot' hStart
  have hZW := ForcingSupportingRoot.code_mem hPres hDcond hS hZ
  have hZStart' := (orderFormula_semantics env (rho 0) mul z start).mpr hZStart
  obtain ⟨_,J,HJ,hJI,hJSmall,hFixJ,hIncluded⟩ := (hFilter S).mp hSF
  obtain ⟨V,hV,hVI,hVSmall⟩ := ConstructionCohenCompatibility.exists_support hM hw hPres.1 hPres.2.1 hDcond
  have hVSmallMu : Small V (env mu) := by
    obtain ⟨toW,hToW⟩ := (ForcingSupportSize.native_small hM _ _).mp hVSmall
    obtain ⟨omegaToMu,hOmegaToMu⟩ := hMu.2
    exact (ForcingSupportSize.native_small hM _ _).mpr (ZF.exists_compositionInjection hZF pair hToW hOmegaToMu)
  obtain ⟨U,hU⟩ := KP.exists_unionOfTwo (ZF.modelsKP hZF) J V
  have hUI : (Project.FirstOrderSemantics.reduct M).MemberSubset U (env I) :=
    fun x hx => ((hU x).mp hx).elim (hJI x) (hVI x)
  have hUSmall : Small U (env mu) := (ForcingSupportSize.native_small hM _ _).mpr
    (ExistingCardinalBounds.infinite_union_two_l pair hZF hw hMu
      ((ForcingSupportSize.native_small hM _ _).mp hJSmall) ((ForcingSupportSize.native_small hM _ _).mp hVSmallMu) hU)
  obtain ⟨p,hp,hPs,hCover⟩ := ConstructionDiagramCoverage.extend_through hM hChoice hw hMu hLarge hCard
    (hm.2.1 (env mark) hMark) hS hUI hUSmall
  obtain ⟨empty,hEmpty⟩ := ForcingWithTopCarrier.exists_empty hM
  obtain ⟨q,hq,hQp,_⟩ := ConstructionDiagramCoverage.extend_through hM hChoice hw hMu hLarge hCard
    (hm.2.1 (env mark) hMark) hp (fun x hx => (hEmpty x hx).elim) (ForcingSupportSize.small_empty hM (env mu) hEmpty)
  have hqp : ForcingDiagramOrder.Le (env (rho 0)) (env mul) q p := ⟨env mark,hMark,hQp⟩
  have hps : ForcingDiagramOrder.Le (env (rho 0)) (env mul) p s := ⟨env mark,hMark,hPs⟩
  obtain ⟨Jp,hJp,_,_⟩ := ConstructionDescentPlacement.diagram_range hM hMu.1.1 hp hD
  obtain ⟨Hp,hHp⟩ := ForcingLabelPermutations.exists_fixing hM (env G) Jp
  obtain ⟨Jq,hJq,hJqI,hJqSmall⟩ := ConstructionDescentPlacement.diagram_range hM hMu.1.1 hq hD
  obtain ⟨Hq,hHq⟩ := ForcingLabelPermutations.exists_fixing hM (env G) Jq
  have hIncludedPS : ∀ pi, (Project.FirstOrderSemantics.reduct M).mem pi Hp →
      (Project.FirstOrderSemantics.reduct M).mem pi S := by
    intro pi hpi
    obtain ⟨hpiG,hpiFix⟩ := (hHp pi).mp hpi
    apply hIncluded pi
    apply (hFixJ pi).mpr
    exact ⟨hpiG,fun x hx => hpiFix x ((hJp x).mpr (hCover x ((hU x).mpr (Or.inl hx))))⟩
  have hDq : ForcingLocalRecordPullback.Supported (env (rho 0)) q d := by
    intro i coordinate bit he
    have hiV := (hV i).mpr ⟨coordinate,bit,he⟩
    exact ConstructionDescentPlacement.range_antitone hqp (hCover i ((hU i).mpr (Or.inr hiV)))
  obtain ⟨zp,hZp⟩ := ForcingSupportingRoot.exists_code hM d p
  obtain ⟨zq,hZq⟩ := ForcingSupportingRoot.exists_code hM d q
  have hZpW := ForcingSupportingRoot.code_mem hPres hDcond hp hZp
  have hZqW := ForcingSupportingRoot.code_mem hPres hDcond hq hZq
  have hZpz := (orderFormula_semantics env (rho 0) mul zp z).mpr
    ((ForcingSupportingRoot.code_le hZp hZ).mpr ⟨fun _ h => h,hps⟩)
  have hZpStart := hpre.2 zp z start hZpW hZW hStart hZpz hZStart'
  have hZqp := (orderFormula_semantics env (rho 0) mul zq zp).mpr
    ((ForcingSupportingRoot.code_le hZq hZp).mpr ⟨fun _ h => h,hqp⟩)
  have hZqStart := hpre.2 zq zp start hZqW hZpW hStart hZqp hZpStart
  have hGroup := ForcingConjugationGraph.fixing_subgroup hM hG hHq hJqI
  have hHqF : (Project.FirstOrderSemantics.reduct M).mem Hq (env F) :=
    (hFilter Hq).mpr ⟨hGroup,Jq,Hq,hJqI,hJqSmall,hHq,fun _ h => h⟩
  exact ⟨d,p,q,Jp,Hp,Jq,Hq,zp,zq,hDcond,hp,hq,hQp,hJp,hHp,hJq,hHq,hIncludedPS,hDq,
    hZp,hZq,hZpW,hZqW,hZpStart,hZqStart,hGroup,hHqF⟩


/-- Only the finite SOURCE parameter context is extended. Family indices
will still range over an arbitrary INTERNAL set, never Fin n. -/
private def extend {α : Type u} {k : Nat} (env : Fin k → α) :
    (n : Nat) → (Fin n → α) → Fin (k+n) → α
  | 0, _ => env
  | n+1, v => Fin.lastCases (v (Fin.last n)) (extend env n (fun j => v j.castSucc))

private theorem extend_base {α : Type u} {k n : Nat} (env : Fin k → α) (v : Fin n → α) (j : Fin k) :
    extend env n v (Fin.castAdd n j) = env j := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change Fin.lastCases (v (Fin.last n)) (extend env n (fun j => v j.castSucc)) (Fin.castAdd n j).castSucc = env j
    rw [Fin.lastCases_castSucc]
    exact ih _

private theorem extend_variable {α : Type u} {k n : Nat} (env : Fin k → α) (v : Fin n → α) (j : Fin n) :
    extend env n v (Fin.natAdd k j) = v j := by
  induction n with
  | zero => exact Fin.elim0 j
  | succ n ih =>
    refine Fin.lastCases ?_ (fun a => ?_) j
    · change Fin.lastCases (v (Fin.last n)) (extend env n (fun j => v j.castSucc)) (Fin.last (k+n)) = v (Fin.last n)
      rw [Fin.lastCases_last]
    · change Fin.lastCases (v (Fin.last n)) (extend env n (fun j => v j.castSucc)) (Fin.natAdd k a).castSucc = v a.castSucc
      rw [Fin.lastCases_castSucc]
      exact ih _ a

private def allParams {k : Nat} : (n : Nat) → Formula (k+n) → Formula k
  | 0, phi => phi
  | n+1, phi => allParams n (.all phi)

private def someParams {k : Nat} : (n : Nat) → Formula (k+n) → Formula k
  | 0, phi => phi
  | n+1, phi => someParams n (.ex phi)

private theorem allParams_semantics {k n : Nat} (env : Fin k → M.Carrier .set) (phi : Formula (k+n)) :
    Formula.Realize (Project.FirstOrderSemantics.reduct M).mem env (allParams n phi) ↔
      ∀ v : Fin n → M.Carrier .set, Formula.Realize (Project.FirstOrderSemantics.reduct M).mem (extend env n v) phi := by
  induction n with
  | zero => exact ⟨fun h _ => h,fun h => h Fin.elim0⟩
  | succ n ih =>
    rw [allParams,ih]
    change (∀ v x, Formula.Realize (Project.FirstOrderSemantics.reduct M).mem
      (Fin.lastCases x (extend env n v)) phi) ↔ _
    constructor
    · intro h v
      exact h (fun j => v j.castSucc) (v (Fin.last n))
    · intro h v x
      simpa only [extend,Fin.lastCases_last,Fin.lastCases_castSucc] using h (Fin.lastCases x v)

private theorem someParams_semantics {k n : Nat} (env : Fin k → M.Carrier .set) (phi : Formula (k+n)) :
    Formula.Realize (Project.FirstOrderSemantics.reduct M).mem env (someParams n phi) ↔
      ∃ v : Fin n → M.Carrier .set, Formula.Realize (Project.FirstOrderSemantics.reduct M).mem (extend env n v) phi := by
  induction n with
  | zero => exact ⟨fun h => ⟨Fin.elim0,h⟩,fun ⟨_,h⟩ => h⟩
  | succ n ih =>
    rw [someParams,ih]
    change (∃ v x, Formula.Realize (Project.FirstOrderSemantics.reduct M).mem
      (Fin.lastCases x (extend env n v)) phi) ↔ _
    constructor
    · rintro ⟨v,x,h⟩
      exact ⟨Fin.lastCases x v,by simpa only [extend,Fin.lastCases_last,Fin.lastCases_castSucc] using h⟩
    · rintro ⟨v,h⟩
      exact ⟨(fun j => v j.castSucc),v (Fin.last n),h⟩

private theorem pointwise (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) {k n : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k)
    (w mu history kappa unit mark H C incoming base I K B G F mul index : Fin k)
    (phi : Formula (n+1)) (v : Fin n → M.Carrier .set)
    (S start d p q Jp Hp Jq Hq zp zq : M.Carrier .set)
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega (env w))
    (hMu : (Project.FirstOrderSemantics.reduct M).IsInfiniteCardinal (KuratowskiZF.interpretation hM) (env w) (env mu))
    (hI : (Project.FirstOrderSemantics.reduct M).IsHartogsNumber (KuratowskiZF.interpretation hM) (env I) (env mu))
    (hD : Small (env (rho 0)) (env mu))
    (hCard : ConstructionSaturationCardinals.Cardinals hM (env (rho 0)) (env mul) (env mark) (env mu))
    (hMergers : ConstructionSaturationMergers.AllMergers (env w) (env history) (env kappa))
    (hRow : ConstructionTowerHistory.Row (env history) (env kappa) (env (rho 0)) (env mul)
      (env unit) (env mark) (env H) (env C) (env incoming) (env base) (env kappa))
    (hm : ForcingDiagramPoset.LeftCancelMonoid (env (rho 0)) (env mul) (env unit))
    (hPres : Presentation (env (rho 0)) (env I) (env K) (env B) (env w)
      (env (rho 1)) (env (rho 2)) (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hG : ForcingLabelPermutations.Carrier (env I) (env G))
    (hFilter : ForcingSupportFilter.Filter (env I) (env G) (env mu) (env F))
    (hMark : (Project.FirstOrderSemantics.reduct M).mem (env mark) (env (rho 0)))
    (hProbes : ForcingRootProbes.RootProbes (env index) (env (rho 0)) (env mul) (env unit) (env mark))
    (hIndex : ¬ Small (env index) (env w))
    (hPrepared : Prepared env rho I G F mul w mark S start d p q Jp Hp Jq Hq zp zq)
    (hv : ∀ j, Supported (fun i => env (rho i)) Hp (v j))
    (hf : Force (orderFormula (rho 0) mul) (domain rho G F) env v (env (rho 6)) zp (.ex phi)) :
    ∃ nu, ForcingHS.HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) nu ∧
      Supported (fun j => env (rho j)) Hq nu ∧
      Force (orderFormula (rho 0) mul) (domain rho G F) env (Fin.lastCases nu v) (env (rho 6)) zq phi := by
  obtain ⟨hd,hp,hq,hSub,hJp,hHp,hJq,hHq,_hIncluded,hdq,hzp,hzq,_hzpW,_hzqW,_hzpStart,_hzqStart,_hGroup,_hHqF⟩ := hPrepared
  let roots : Fin (k+9) → M.Carrier .set := Fin.cases zq (Fin.cases zp (Fin.cases Hq (Fin.cases Jq
    (Fin.cases Hp (Fin.cases Jp (Fin.cases q (Fin.cases p (Fin.cases d env))))))))
  let other := extend roots n v
  let rootSlot (j : Fin 9) : Fin (k+9+n) := Fin.castAdd n (⟨j.val,by omega⟩ : Fin (k+9))
  let up (j : Fin k) : Fin (k+9+n) := Fin.castAdd n j.succ.succ.succ.succ.succ.succ.succ.succ.succ
  let ra : Fin 7 → Fin (k+9+n) := fun j => up (rho j)
  let slots : Fin n → Fin (k+9+n) := Fin.natAdd (k+9)
  have hb (j : Fin 9) : other (rootSlot j) = roots (⟨j.val,by omega⟩ : Fin (k+9)) := extend_base roots v _
  have he (j : Fin k) : other (up j) = env j := by
    change extend roots n v (Fin.castAdd n j.succ.succ.succ.succ.succ.succ.succ.succ.succ) = env j
    rw [extend_base]
    rfl
  have hr0 : other (rootSlot 0) = zq := by rw [hb]; rfl
  have hr1 : other (rootSlot 1) = zp := by rw [hb]; rfl
  have hr2 : other (rootSlot 2) = Hq := by rw [hb]; rfl
  have hr3 : other (rootSlot 3) = Jq := by rw [hb]; rfl
  have hr4 : other (rootSlot 4) = Hp := by rw [hb]; rfl
  have hr5 : other (rootSlot 5) = Jp := by rw [hb]; rfl
  have hr6 : other (rootSlot 6) = q := by rw [hb]; rfl
  have hr7 : other (rootSlot 7) = p := by rw [hb]; rfl
  have hr8 : other (rootSlot 8) = d := by rw [hb]; rfl
  have hvv (j : Fin n) : other (slots j) = v j := extend_variable roots v j
  have hR (a b : M.Carrier .set) : MapRel (orderFormula (rho 0) mul) env a b ↔
      MapRel (orderFormula (ra 0) (up mul)) other a b := by
    simp only [orderFormula_semantics,ra,he]
  have hH (a : M.Carrier .set) : ForcingClassEvaluation.Predicate (domain rho G F) env a ↔
      ForcingClassEvaluation.Predicate (domain ra (up G) (up F)) other a := by
    simp only [domain_semantics,ra,he]
  have hf' := (ForcingSeparation.force_congr hR hH (.ex phi) v (env (rho 6)) zp).mp hf
  obtain ⟨nu,out,hNuHS,hNuFix,hOut,hForce⟩ := ForcingLocalizedMaximum.localized_maximum hM hChoice other ra
    (up w) (up mu) (up history) (up kappa) (up unit) (up mark) (up H) (up C) (up incoming) (up base)
    (up I) (up K) (up B) (up G) (up F) (up mul) (up index) (rootSlot 7) (rootSlot 6) (rootSlot 8) (rootSlot 5) (rootSlot 4) (rootSlot 3) (rootSlot 2) (rootSlot 1)
    phi slots
    (by simpa only [he] using hw)
    (by simpa only [he] using hMu)
    (by simpa only [he] using hI)
    (by simpa only [ra,he] using hD)
    (by simpa only [ra,he] using hCard)
    (by simpa only [he] using hMergers)
    (by simpa only [ra,he] using hRow)
    (by simpa only [ra,he] using hm)
    (by simpa only [ra,he] using hPres)
    (by simpa only [he] using hG)
    (by simpa only [he] using hFilter)
    (by simpa only [ra,he] using hMark)
    (by simpa only [ra,he] using hProbes)
    (by simpa only [he] using hIndex)
    (by simpa only [ra,he,hr0,hr1,hr2,hr3,hr4,hr5,hr6,hr7,hr8] using hp)
    (by simpa only [ra,he,hr0,hr1,hr2,hr3,hr4,hr5,hr6,hr7,hr8] using hq)
    (by simpa only [ra,he,hr0,hr1,hr2,hr3,hr4,hr5,hr6,hr7,hr8] using hSub)
    (by simpa only [ra,he,hr0,hr1,hr2,hr3,hr4,hr5,hr6,hr7,hr8] using hJp)
    (by simpa only [ra,he,hr0,hr1,hr2,hr3,hr4,hr5,hr6,hr7,hr8] using hHp)
    (by simpa only [ra,he,hr0,hr1,hr2,hr3,hr4,hr5,hr6,hr7,hr8] using hJq)
    (by simpa only [ra,he,hr0,hr1,hr2,hr3,hr4,hr5,hr6,hr7,hr8] using hHq)
    (by simpa only [ra,he,hr0,hr1,hr2,hr3,hr4,hr5,hr6,hr7,hr8,hvv] using hv)
    (by simpa only [ra,he,hr0,hr1,hr2,hr3,hr4,hr5,hr6,hr7,hr8] using hd)
    (by simpa only [ra,he,hr0,hr1,hr2,hr3,hr4,hr5,hr6,hr7,hr8] using hdq)
    (by simpa only [ra,he,hr0,hr1,hr2,hr3,hr4,hr5,hr6,hr7,hr8] using hzp)
    (by simpa only [ra,he,hr0,hr1,hr2,hr3,hr4,hr5,hr6,hr7,hr8,hvv] using hf')
  have hOut' : Code out d q := by
    simpa only [hr0,hr1,hr2,hr3,hr4,hr5,hr6,hr7,hr8] using hOut
  obtain ⟨c,hc,hs⟩ := hOut'
  obtain ⟨c',hc',hs'⟩ := hzq
  have hcc := KuratowskiZF.code_unique hM hc' hc
  subst c'
  have heq : out = zq := ForcingWithTopCarrier.single_unique hM hs hs'
  rw [heq] at hForce
  refine ⟨nu,?_,?_,?_⟩
  · simpa only [ra,he] using hNuHS
  · simpa only [ra,he,hr0,hr1,hr2,hr3,hr4,hr5,hr6,hr7,hr8] using hNuFix
  · apply (ForcingSeparation.force_congr hR hH phi (Fin.lastCases nu v) (env (rho 6)) zq).mpr
    simpa only [ra,he,hvv] using hForce


/-- An internally definable parameter family. n is SOURCE formula arity;
i ranges over an arbitrary internal set in the actual family theorem. -/
def ParameterSpec {k n : Nat} (env : Fin k → M.Carrier .set) (Q : Formula (k+1+n))
    (i : M.Carrier .set) (v : Fin n → M.Carrier .set) : Prop :=
  Formula.Realize (Project.FirstOrderSemantics.reduct M).mem (extend (Fin.lastCases i env) n v) Q

def Selected {k n : Nat} (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k)
    (G F mul : Fin k) (Hq zq : M.Carrier .set) (Q : Formula (k+1+n)) (phi : Formula (n+1)) (i nu : M.Carrier .set) : Prop :=
  ForcingHS.HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) nu ∧
    Supported (fun j => env (rho j)) Hq nu ∧
      ∀ v, ParameterSpec env Q i v → Force (orderFormula (rho 0) mul) (domain rho G F) env
        (Fin.lastCases nu v) (env (rho 6)) zq phi

/-- The extra base context holds actual, newly constructed Hq/zq witnesses.
It changes no ground parameter, source formula or internal index family. -/
def selected {k m n : Nat} (base : Fin k → Fin m) (rho : Fin 7 → Fin k) (G F mul : Fin k)
    (Hq zq : Fin m) (Q : Formula (k+1+n)) (phi : Formula (n+1)) : Formula (m+2) :=
  let b : Fin k → Fin (m+2+n) := fun j => Fin.castAdd n (base j).castSucc.castSucc
  let liftQ : Fin (k+1+n) → Fin (m+2+n) :=
    Fin.addCases (Fin.lastCases (Fin.castAdd n (Fin.last m).castSucc) b) (Fin.natAdd (m+2))
  let rr : Fin 7 → Fin (m+2) := fun j => (base (rho j)).castSucc.castSucc
  let nu := Fin.last (m+1)
  (ForcingHS.hs actionFormula rr (base G).castSucc.castSucc (base (rho 6)).castSucc.castSucc (base F).castSucc.castSucc nu).conj
    ((ForcingEquivariantMix.fixedAll rr Hq.castSucc.castSucc nu).conj
      (allParams n ((Q.rename liftQ).imp
        (ForcingFormula.formula (orderFormula (rho 0) mul) (domain rho G F) b
          (Fin.lastCases (Fin.castAdd n nu) (Fin.natAdd (m+2))) (b (rho 6)) (Fin.castAdd n zq.castSucc.castSucc) phi))))

theorem selected_semantics {k m n : Nat} (env : Fin m → M.Carrier .set) (base : Fin k → Fin m)
    (rho : Fin 7 → Fin k) (G F mul : Fin k) (Hq zq : Fin m) (Q : Formula (k+1+n))
    (phi : Formula (n+1)) (i nu : M.Carrier .set) :
    Formula.Realize (Project.FirstOrderSemantics.reduct M).mem (Fin.lastCases nu (Fin.lastCases i env))
      (selected base rho G F mul Hq zq Q phi) ↔
        Selected (fun j => env (base j)) rho G F mul (env Hq) (env zq) Q phi i nu := by
  have hQ (v : Fin n → M.Carrier .set) :
      (fun j => extend (Fin.lastCases nu (Fin.lastCases i env)) n v
        (Fin.addCases (Fin.lastCases (Fin.castAdd n (Fin.last m).castSucc)
          (fun j => Fin.castAdd n (base j).castSucc.castSucc)) (Fin.natAdd (m+2)) j)) =
        extend (Fin.lastCases i (fun j => env (base j))) n v := by
    funext j
    refine Fin.addCases (fun a => ?_) (fun a => ?_) j
    · refine Fin.lastCases ?_ (fun b => ?_) a
      · simp only [Fin.addCases_left,Fin.lastCases_last,extend_base,Fin.lastCases_castSucc,Fin.lastCases_last]
      · simp only [Fin.addCases_left,Fin.lastCases_castSucc,extend_base]
    · simp only [Fin.addCases_right,extend_variable]
  have hTuple (v : Fin n → M.Carrier .set) :
      (fun j => extend (Fin.lastCases nu (Fin.lastCases i env)) n v
        (Fin.lastCases (Fin.castAdd n (Fin.last (m+1))) (Fin.natAdd (m+2)) j)) = Fin.lastCases nu v := by
    funext j
    refine Fin.lastCases ?_ (fun a => ?_) j
    · simp only [Fin.lastCases_last,extend_base,Fin.lastCases_last]
    · simp only [Fin.lastCases_castSucc,extend_variable]
  simp only [selected,Selected,ParameterSpec,Formula.Realize,ForcingHS.hs_semantics (M := M),
    ForcingEquivariantMix.fixedAll_semantics,allParams_semantics,DefinableMinimaChoice.realize_rename,
    ForcingFormula.formula_semantics,Fin.lastCases_last,Fin.lastCases_castSucc]
  simp only [hQ,hTuple,extend_base,Fin.lastCases_castSucc]
  rfl

/-- Collection bounds the exact selected-name predicate; the ALREADY REUSED
bounded uniformization constructs one INTERNAL function graph on all of X. -/
theorem choose_family (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) {k n : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (G F mul : Fin k)
    (Hq zq X : M.Carrier .set) (Q : Formula (k+1+n)) (phi : Formula (n+1))
    (hEach : ∀ i, (Project.FirstOrderSemantics.reduct M).mem i X → ∃ nu,
      Selected env rho G F mul Hq zq Q phi i nu) :
    ∃ f, FunctionOn X f ∧ ∀ i nu, PureKuratowski.PairMember M i nu f →
      Selected env rho G F mul Hq zq Q phi i nu := by
  let other : Fin (k+3) → M.Carrier .set := Fin.cases X (Fin.cases zq (Fin.cases Hq env))
  let base : Fin k → Fin (k+3) := fun j => j.succ.succ.succ
  let hqIndex : Fin (k+3) := (0 : Fin (k+1)).succ.succ
  let zqIndex : Fin (k+3) := (0 : Fin (k+2)).succ
  let reorder : Fin (k+3+2) → Fin (k+3+2) :=
    Fin.lastCases 0 (Fin.lastCases (Fin.succ (0 : Fin (k+3+1))) (fun j => j.succ.succ))
  let schema : Project.BinarySchema (k+3) := {
    body := ProjectSyntax.encode reorder (selected base rho G F mul hqIndex zqIndex Q phi)
    freeClosed := ProjectSyntax.freeClosed .. }
  let penv : Env (Project.FirstOrderSemantics.reduct M) (k+3) := ⟨other,fun _ => X⟩
  have he i nu : schema.denote penv i nu ↔ Selected env rho G F mul Hq zq Q phi i nu := by
    change Project.Formula.satisfies ((penv.push i).push nu)
      (ProjectSyntax.encode reorder (selected base rho G F mul hqIndex zqIndex Q phi)) ↔ _
    rw [GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM)]
    have hEnv : (fun j => ((penv.push i).push nu).bound (reorder j)) = Fin.lastCases nu (Fin.lastCases i other) := by
      funext j
      refine Fin.lastCases ?_ (fun a => ?_) j
      · simp only [reorder,Fin.lastCases_last,SetTheory.Env.push,Fin.cases_zero]
      · refine Fin.lastCases ?_ (fun a => ?_) a
        · simp only [reorder,Fin.lastCases_castSucc,Fin.lastCases_last,SetTheory.Env.push,Fin.cases_succ,Fin.cases_zero]
        · simp only [reorder,Fin.lastCases_castSucc,SetTheory.Env.push,Fin.cases_succ,penv]
    rw [hEnv,selected_semantics]
    rfl
  obtain ⟨names,hNames⟩ := ZF.collection_exists_d (ModelTransfer.project_models_iff.mp hM) schema penv X
    (fun i hi => by obtain ⟨nu,hnu⟩ := hEach i hi; exact ⟨nu,(he i nu).mpr hnu⟩)
  obtain ⟨f,hf,hSelect⟩ := ExistingSmallUnion.uniformize_formula_l (KuratowskiZF.interpretation hM)
    (ConstructionDirectedCardinality.models_zfc hM hChoice) schema penv (X := X) (Y := names) hNames
  exact ⟨f,((ForcingSupportSize.native_mapsTo hM _ _ _).mpr hf).1,fun i nu h => (he i nu).mp (hSelect i nu h)⟩

/-- Exact source parameter-family inputs. Functionality is on the INTERNAL
index set; there is no host-selected parameter family or external wellorder. -/
def Inputs {k n : Nat} (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k)
    (G F mul : Fin k) (S start X : M.Carrier .set) (Q : Formula (k+1+n)) (phi : Formula (n+1)) : Prop :=
  (∀ i, (Project.FirstOrderSemantics.reduct M).mem i X → ∃ v, ParameterSpec env Q i v) ∧
  (∀ i, (Project.FirstOrderSemantics.reduct M).mem i X → ∀ v v', ParameterSpec env Q i v → ParameterSpec env Q i v' → v = v') ∧
  (∀ i, (Project.FirstOrderSemantics.reduct M).mem i X → ∀ v, ParameterSpec env Q i v →
    ∀ j, Supported (fun a => env (rho a)) S (v j)) ∧
  (∀ i, (Project.FirstOrderSemantics.reduct M).mem i X → ∀ v, ParameterSpec env Q i v →
    Force (orderFormula (rho 0) mul) (domain rho G F) env v (env (rho 6)) start (.ex phi))

def Result {k n : Nat} (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k)
    (I G F mul : Fin k) (start X : M.Carrier .set) (Q : Formula (k+1+n)) (phi : Formula (n+1)) : Prop :=
  ∃ out Hq f, (Project.FirstOrderSemantics.reduct M).mem out (env (rho 6)) ∧
    MapRel (orderFormula (rho 0) mul) env out start ∧ ForcingConjugationGraph.Subgroup (env I) (env G) Hq ∧
    (Project.FirstOrderSemantics.reduct M).mem Hq (env F) ∧ FunctionOn X f ∧
    ∀ i nu, PureKuratowski.PairMember M i nu f → Selected env rho G F mul Hq out Q phi i nu

theorem uniform_maximum_dense (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) {k n : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k)
    (w mu history kappa unit mark H C incoming base I K B G F mul index : Fin k)
    (Q : Formula (k+1+n)) (phi : Formula (n+1)) (S start X : M.Carrier .set)
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega (env w))
    (hMu : (Project.FirstOrderSemantics.reduct M).IsInfiniteCardinal (KuratowskiZF.interpretation hM) (env w) (env mu))
    (hI : (Project.FirstOrderSemantics.reduct M).IsHartogsNumber (KuratowskiZF.interpretation hM) (env I) (env mu))
    (hD : Small (env (rho 0)) (env mu))
    (hCard : ConstructionSaturationCardinals.Cardinals hM (env (rho 0)) (env mul) (env mark) (env mu))
    (hMergers : ConstructionSaturationMergers.AllMergers (env w) (env history) (env kappa))
    (hRow : ConstructionTowerHistory.Row (env history) (env kappa) (env (rho 0)) (env mul)
      (env unit) (env mark) (env H) (env C) (env incoming) (env base) (env kappa))
    (hm : ForcingDiagramPoset.LeftCancelMonoid (env (rho 0)) (env mul) (env unit))
    (hPres : Presentation (env (rho 0)) (env I) (env K) (env B) (env w)
      (env (rho 1)) (env (rho 2)) (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hG : ForcingLabelPermutations.Carrier (env I) (env G))
    (hFilter : ForcingSupportFilter.Filter (env I) (env G) (env mu) (env F))
    (hMark : (Project.FirstOrderSemantics.reduct M).mem (env mark) (env (rho 0)))
    (hProbes : ForcingRootProbes.RootProbes (env index) (env (rho 0)) (env mul) (env unit) (env mark))
    (hIndex : ¬ Small (env index) (env w))
    (hSF : (Project.FirstOrderSemantics.reduct M).mem S (env F))
    (hStart : (Project.FirstOrderSemantics.reduct M).mem start (env (rho 6)))
    (hInputs : Inputs env rho G F mul S start X Q phi) : Result env rho I G F mul start X Q phi := by
  obtain ⟨d,p,q,Jp,Hp,Jq,Hq,zp,zq,hPrepared⟩ := prepare hM hChoice env rho w mu unit mark I K B G F mul
    hw hMu hI hD hCard hm hPres hG hFilter hMark hSF hStart
  have hPreparedCopy := hPrepared
  obtain ⟨_hd,_hp,_hq,_hSub,_hJp,_hHp,_hJq,_hHq,hIncluded,_hdq,_hzp,_hzq,hzpW,hzqW,hzpStart,hzqStart,hGroup,hHqF⟩ := hPrepared
  obtain ⟨hTotal,hUnique,hFixed,hForce⟩ := hInputs
  have hpre := ForcingProductPoset.preorder env (rho 0) mul (rho 6) hm
    hPres.2.2.2.2.1 hPres.2.2.2.1 hPres.2.2.2.2.2
  have hEach : ∀ i, (Project.FirstOrderSemantics.reduct M).mem i X → ∃ nu,
      Selected env rho G F mul Hq zq Q phi i nu := by
    intro i hi
    obtain ⟨v,hSpec⟩ := hTotal i hi
    have hv : ∀ j, Supported (fun a => env (rho a)) Hp (v j) := by
      intro j pi hpi act hAct
      exact hFixed i hi v hSpec j pi (hIncluded pi hpi) act hAct
    have hInput := ForcingFormula.mono hM hpre (.ex phi) v hStart hzpW hzpStart (hForce i hi v hSpec)
    obtain ⟨nu,hHS,hSupport,hForced⟩ := pointwise hM hChoice env rho
      w mu history kappa unit mark H C incoming base I K B G F mul index phi v
      S start d p q Jp Hp Jq Hq zp zq hw hMu hI hD hCard hMergers hRow hm hPres hG hFilter hMark hProbes hIndex
      hPreparedCopy hv hInput
    refine ⟨nu,hHS,hSupport,?_⟩
    intro v' hSpec'
    have heq := hUnique i hi v v' hSpec hSpec'
    cases heq
    exact hForced
  obtain ⟨f,hf,hSelected⟩ := choose_family hM hChoice env rho G F mul Hq zq X Q phi hEach
  exact ⟨zq,Hq,f,hzqW,hzqStart,hGroup,hHqF,hf,hSelected⟩

/-- One actual internal function graph, including original functionOn,
common support and the SAME condition for every index and parameter tuple. -/
def resultFormula {k n : Nat} (rho : Fin 7 → Fin k) (I G F mul start X : Fin k)
    (Q : Formula (k+1+n)) (phi : Formula (n+1)) : Formula k :=
  let b : Fin k → Fin (k+3) := fun j => j.castSucc.castSucc.castSucc
  let out := (Fin.last k).castSucc.castSucc
  let Hq := (Fin.last (k+1)).castSucc
  let f := Fin.last (k+2)
  .ex (.ex (.ex ((Formula.mem out (b (rho 6))).conj
    ((ReplacementPredicates.rel (orderFormula (rho 0) mul) b out (b start)).conj
      ((ForcingConjugationGraph.subgroup (b I) (b G) Hq).conj
        ((Formula.mem Hq (b F)).conj ((Source.SetLanguage.functionOn f (b X)).conj
          (.all (.all ((Source.SetLanguage.edge f.castSucc.castSucc (Fin.last (k+3)).castSucc (Fin.last (k+4))).imp
            (selected b rho G F mul Hq out Q phi)))))))))))

theorem resultFormula_semantics {k n : Nat} (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k)
    (I G F mul start X : Fin k) (Q : Formula (k+1+n)) (phi : Formula (n+1)) :
    Formula.Realize (Project.FirstOrderSemantics.reduct M).mem env (resultFormula rho I G F mul start X Q phi) ↔
      Result env rho I G F mul (env start) (env X) Q phi := by
  simp only [resultFormula,Result,Formula.Realize,ForcingMapConditions.rel_semantics (M := M),
    ForcingConjugationGraph.subgroup_semantics,ForcingConditionGraphs.functionOn_semantics (M := M),
    KuratowskiZF.source_edge,selected_semantics,Fin.lastCases_last,Fin.lastCases_castSucc]
  rfl


private def totalFormula {k n : Nat} (X : Fin k) (Q : Formula (k+1+n)) : Formula k :=
  .all ((Formula.mem (Fin.last k) X.castSucc).imp (someParams n Q))

private theorem totalFormula_semantics {k n : Nat} (env : Fin k → M.Carrier .set) (X : Fin k) (Q : Formula (k+1+n)) :
    Formula.Realize (Project.FirstOrderSemantics.reduct M).mem env (totalFormula X Q) ↔
      ∀ i, (Project.FirstOrderSemantics.reduct M).mem i (env X) → ∃ v, ParameterSpec env Q i v := by
  simp only [totalFormula,Formula.Realize,someParams_semantics,ParameterSpec,Fin.lastCases_castSucc,Fin.lastCases_last]

private def uniqueFormula {k n : Nat} (X : Fin k) (Q : Formula (k+1+n)) : Formula k :=
  let second : Fin (k+1+n) → Fin (k+1+n+n) :=
    Fin.addCases (fun j => Fin.castAdd n (Fin.castAdd n j)) (Fin.natAdd (k+1+n))
  let equations : Formula (k+1+n+n) := ForcingSound.conjunction ((List.finRange n).map (fun j =>
    Formula.equal (Fin.castAdd n (Fin.natAdd (k+1) j)) (Fin.natAdd (k+1+n) j)))
  .all ((Formula.mem (Fin.last k) X.castSucc).imp
    (allParams n (allParams n ((Q.rename (Fin.castAdd n)).imp ((Q.rename second).imp equations)))))

private theorem uniqueFormula_semantics {k n : Nat} (env : Fin k → M.Carrier .set) (X : Fin k) (Q : Formula (k+1+n)) :
    Formula.Realize (Project.FirstOrderSemantics.reduct M).mem env (uniqueFormula X Q) ↔
      ∀ i, (Project.FirstOrderSemantics.reduct M).mem i (env X) → ∀ v v',
        ParameterSpec env Q i v → ParameterSpec env Q i v' → v = v' := by
  have hQ (i : M.Carrier .set) (v v' : Fin n → M.Carrier .set) :
      (fun j => extend (extend (Fin.lastCases i env) n v) n v'
        (Fin.addCases (fun j => Fin.castAdd n (Fin.castAdd n j)) (Fin.natAdd (k+1+n)) j)) =
        extend (Fin.lastCases i env) n v' := by
    funext j
    refine Fin.addCases (fun a => ?_) (fun a => ?_) j
    · simp only [Fin.addCases_left,extend_base]
    · simp only [Fin.addCases_right,extend_variable]
  simp only [uniqueFormula,Formula.Realize,allParams_semantics,DefinableMinimaChoice.realize_rename,
    ForcingTupleStabilizer.finite_conjunction,extend_base,extend_variable,hQ,ParameterSpec,
    Fin.lastCases_castSucc,Fin.lastCases_last]
  constructor
  · intro h i hi v v' hv hv'
    exact funext (h i hi v v' hv hv')
  · intro h i hi v v' hv hv' j
    exact congrFun (h i hi v v' hv hv') j

private def fixedInput {k n : Nat} (rho : Fin 7 → Fin k) (S X : Fin k) (Q : Formula (k+1+n)) : Formula k :=
  let b : Fin k → Fin (k+1+n) := fun j => Fin.castAdd n j.castSucc
  .all ((Formula.mem (Fin.last k) X.castSucc).imp (allParams n (Q.imp
    (ForcingSupportingRoot.tupleSupported (fun j => b (rho j)) (b S) (Fin.natAdd (k+1))))))

private theorem fixedInput_semantics {k n : Nat} (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k)
    (S X : Fin k) (Q : Formula (k+1+n)) :
    Formula.Realize (Project.FirstOrderSemantics.reduct M).mem env (fixedInput rho S X Q) ↔
      ∀ i, (Project.FirstOrderSemantics.reduct M).mem i (env X) → ∀ v, ParameterSpec env Q i v →
        ∀ j, Supported (fun a => env (rho a)) (env S) (v j) := by
  simp only [fixedInput,Formula.Realize,allParams_semantics,ForcingSupportingRoot.tupleSupported_semantics (M := M),
    extend_base,extend_variable,ParameterSpec,Fin.lastCases_castSucc,Fin.lastCases_last]

private def forcedInput {k n : Nat} (rho : Fin 7 → Fin k) (G F mul start X : Fin k)
    (Q : Formula (k+1+n)) (phi : Formula (n+1)) : Formula k :=
  let b : Fin k → Fin (k+1+n) := fun j => Fin.castAdd n j.castSucc
  .all ((Formula.mem (Fin.last k) X.castSucc).imp (allParams n (Q.imp
    (ForcingFormula.formula (orderFormula (rho 0) mul) (domain rho G F) b
      (Fin.natAdd (k+1)) (b (rho 6)) (b start) (.ex phi)))))

private theorem forcedInput_semantics {k n : Nat} (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k)
    (G F mul start X : Fin k) (Q : Formula (k+1+n)) (phi : Formula (n+1)) :
    Formula.Realize (Project.FirstOrderSemantics.reduct M).mem env (forcedInput rho G F mul start X Q phi) ↔
      ∀ i, (Project.FirstOrderSemantics.reduct M).mem i (env X) → ∀ v, ParameterSpec env Q i v →
        Force (orderFormula (rho 0) mul) (domain rho G F) env v (env (rho 6)) (env start) (.ex phi) := by
  simp only [forcedInput,Formula.Realize,allParams_semantics,ForcingFormula.formula_semantics,
    extend_base,extend_variable,ParameterSpec,Fin.lastCases_castSucc,Fin.lastCases_last]

def inputs {k n : Nat} (rho : Fin 7 → Fin k) (G F mul S start X : Fin k)
    (Q : Formula (k+1+n)) (phi : Formula (n+1)) : Formula k :=
  (totalFormula X Q).conj ((uniqueFormula X Q).conj ((fixedInput rho S X Q).conj
    (forcedInput rho G F mul start X Q phi)))

theorem inputs_semantics {k n : Nat} (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k)
    (G F mul S start X : Fin k) (Q : Formula (k+1+n)) (phi : Formula (n+1)) :
    Formula.Realize (Project.FirstOrderSemantics.reduct M).mem env (inputs rho G F mul S start X Q phi) ↔
      Inputs env rho G F mul (env S) (env start) (env X) Q phi := by
  simp only [inputs,Inputs,Formula.Realize,totalFormula_semantics,uniqueFormula_semantics,fixedInput_semantics,forcedInput_semantics]


def sentence {k n : Nat} (rho : Fin 7 → Fin k)
    (w mu history kappa unit mark H C incoming base I K B G F mul index S start X : Fin k)
    (Q : Formula (k+1+n)) (phi : Formula (n+1)) : Project.Sentence where
  formula := Project.Formula.forallClosure k
    ([Project.Formula.isOmega (.bound w),
      Project.Formula.isInfiniteCardinal PureKuratowskiProject.convention (.bound w) (.bound mu),
      ConstructionSaturationIndex.hartogs mu I,
      ProjectSyntax.encode id (ForcingSupportSize.small (rho 0) mu),
      ConstructionSaturationCardinals.cardinalsF (rho 0) mul mark mu,
      ConstructionSaturationMergers.allMergers w history kappa,
      ConstructionTowerHistory.row history kappa (rho 0) mul unit mark H C incoming base kappa,
      ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid (rho 0) mul unit),
      ProjectSyntax.encode id (ForcingProductFamily.presentation (rho 0) I K B w (rho 1) (rho 2) (rho 3) (rho 4) (rho 5) (rho 6)),
      ProjectSyntax.encode id (ForcingLabelPermutations.carrier I G),
      ProjectSyntax.encode id (ForcingSupportFilter.filter I G mu F),
      .mem (.bound mark) (.bound (rho 0)),
      ForcingRootProbes.rootProbes index (rho 0) mul unit mark,
      .neg (ProjectSyntax.encode id (ForcingSupportSize.small index w)),
      .mem (.bound S) (.bound F),
      .mem (.bound start) (.bound (rho 6)),
      ProjectSyntax.encode id (inputs rho G F mul S start X Q phi)].foldr Definitional.Formula.imp
        (ProjectSyntax.encode id (resultFormula rho I G F mul start X Q phi)))
  freeClosed := by
    simp -implicitDefEqProofs [List.foldr,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
      Project.Formula.isOmega,Project.Formula.isInfiniteCardinal,ConstructionSaturationIndex.hartogs_freeClosed,
      ConstructionSaturationCardinals.cardinalsF_freeClosed,ConstructionSaturationMergers.allMergers_freeClosed,
      ConstructionTowerHistory.row_freeClosed,ForcingRootProbes.rootProbes_freeClosed]

theorem models {k n : Nat} (rho : Fin 7 → Fin k)
    (w mu history kappa unit mark H C incoming base I K B G F mul index S start X : Fin k)
    (Q : Formula (k+1+n)) (phi : Formula (n+1))
    (hM : FirstOrder.Theory.Models M nativeZF) (hChoice : ConstructionDirectedCardinality.Choice (M := M)) :
    (Project.fo_sentence (sentence rho w mu history kappa unit mark H C incoming base I K B G F mul index S start X Q phi)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM),SetTheory.Structure.satisfiesSentence_iff]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro env
  simp only [List.foldr,Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_isOmega_iff,
    Project.Formula.satisfies_isInfiniteCardinal_iff (KuratowskiZF.interpretation hM) (ModelTransfer.extensionality hM),
    Project.Formula.satisfies_neg_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    ConstructionSaturationIndex.hartogs_semantics hM,ConstructionSaturationCardinals.cardinalsF_semantics hM,
    ConstructionSaturationMergers.allMergers_semantics hM,ConstructionTowerHistory.row_semantics hM,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ForcingSupportSize.small_semantics (M := M),
    ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),ForcingProductFamily.presentation_semantics (M := M),
    ForcingLabelPermutations.carrier_semantics (M := M),ForcingSupportFilter.filter_semantics (M := M),
    ForcingRootProbes.rootProbes_semantics hM,inputs_semantics,resultFormula_semantics,id_eq]
  intro hw hMu hI hD hCard hMergers hRow hm hPres hG hFilter hMark hProbes hIndex hSF hStart hInputs
  exact uniform_maximum_dense hM hChoice env rho w mu history kappa unit mark H C incoming base I K B G F mul index
    Q phi (env S) (env start) (env X) hw hMu hI hD hCard hMergers hRow hm hPres hG hFilter hMark hProbes hIndex hSF hStart hInputs

/-- Existing internal L discharges the source ground Choice. The ordinary
nativeZF original kernel proves the SAME L-relative uniform FAMILY theorem. -/
theorem kernel_certificate {k n : Nat} (rho : Fin 7 → Fin k)
    (w mu history kappa unit mark H C incoming base I K B G F mul index S start X : Fin k)
    (Q : Formula (k+1+n)) (phi : Formula (n+1)) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (ConstructibleGround.relative
      (sentence rho w mu history kappa unit mark H C incoming base I K B G F mul index S start X Q phi))) := by
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
    (models rho w mu history kappa unit mark H C incoming base I K B G F mul index S start X Q phi hL hChoice)

end PPAC.Migration.ForcingUniformMaximum
