/- Pinned Main.reverse_injection_dense:133-148. All-set source reduction:
existing ordinal_presentation and actual slice presentation in the nonempty
case; existing empty-domain injection in the empty case. No new foundation. -/
import PPAC.Migration.ForcingSlicePresentation
import PPAC.Migration.ForcingPresentationCover

namespace PPAC.Migration.ForcingReverseInjection
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open Source (Formula)
open Source.SetLanguage (args1 args2 args3)
open ForcingMapConditions (MapRel)
open ForcingAtomicRelations (Forces)
open ForcingFormula (Force)
open ForcingClassEvaluation (Predicate)
open ForcingProductFamily (Presentation actionFormula)
open ForcingProductSymmetry (orderFormula orderFormula_semantics)
open ForcingPairUnion (domain domain_semantics)
open ForcingHS (HS)
open ForcingSupportedNames (Supported)
open ForcingConcreteSystem (forcingRho)
open ForcingNonwellorderableImage (force_reindex pre_reindex)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 400000
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

private abbrev coreRho {k : Nat} (root : Fin 40 → Fin k) : Fin 7 → Fin k := fun j => root (forcingRho j)

private abbrev MapForce {k : Nat} (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k)
    (G F mul : Fin k) (f X Y p : M.Carrier .set) (phi : Formula 3) : Prop :=
  Force (orderFormula (rho 0) mul) (domain rho G F) env (args3 f X Y) (env (rho 6)) p phi

/-- Only the existing native ordinal interface is unpacked into the completed
source ordinal syntax. Every INTERNAL subset remains quantified. -/
private theorem ordinal_raw (hM : FirstOrder.Theory.Models M nativeZF) {a : M.Carrier .set}
    (h : (Project.FirstOrderSemantics.reduct M).IsOrdinal a) : ForcingRawRank.Ordinal a := by
  simp only [ForcingRawRank.Ordinal,OrdinalSyntax.ordinal,OrdinalSyntax.transitiveSet,
    OrdinalSyntax.linear,OrdinalSyntax.irreflexive,OrdinalSyntax.membershipTransitive,
    OrdinalSyntax.comparable,OrdinalSyntax.wellFounded,OrdinalSyntax.minimalExists,
    OrdinalSyntax.setMinimal,RestrictionSyntax.subset,MinimalPredicates.inhabited,
    Source.Formula.Realize,Source.Formula.neg,Fin.lastCases_last,Fin.lastCases_castSucc]
  refine ⟨?_,⟨h.wellOrder.linear.irrefl,?_,?_⟩,?_⟩
  · intro x y hx hy
    exact h.1 x hx y hy
  · intro x y z hx hy hz hxy
    exact h.wellOrder.linear.trans x hx y hy z hz hxy.1 hxy.2
  · intro x y hx hy
    rcases h.wellOrder.linear.compare x hx y hy with he | hxy | hyx
    · exact Or.inl ((ModelTransfer.extensionality hM).eq_of_same_members x y he)
    · exact Or.inr (Or.inl hxy)
    · exact Or.inr (Or.inr hyx)
  · intro b hb
    obtain ⟨x,hx,hmin⟩ := h.2.2 b hb.1 hb.2
    refine ⟨x,hx,?_⟩
    intro y hy hyx
    rcases hmin y hy with he | hxy
    · have heq := (ModelTransfer.extensionality hM).eq_of_same_members x y he
      cases heq
      exact h.wellOrder.linear.irrefl x (hb.1 x hx) hyx
    · exact h.wellOrder.linear.irrefl x (hb.1 x hx) (h.wellOrder.linear.trans x (hb.1 x hx) y (hb.1 y hy) x (hb.1 x hx) hxy hyx)

/-- The ALREADY completed ordinal_presentation, with every source parent
read from the SAME Core. No ordinal/presentation/support is supplied. -/
private theorem present_on_core (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) {k : Nat}
    (env : Fin k → M.Carrier .set) (root : Fin 40 → Fin k) (X x0 : Fin k)
    (hCore : ForcingConcreteSystem.Core hM (fun j => env (root j)))
    (hX : HS actionFormula (fun j => env (coreRho root j)) (env (root 34)) (env (coreRho root 6)) (env (root 35)) (env X))
    (hX0 : HS actionFormula (fun j => env (coreRho root j)) (env (root 34)) (env (coreRho root 6)) (env (root 35)) (env x0))
    {p : M.Carrier .set} (hp : (Project.FirstOrderSemantics.reduct M).mem p (env (coreRho root 6)))
    (hx0 : Forces false (orderFormula (coreRho root 0) (root 18)) env (env (coreRho root 6)) (env x0) (env X) p) :
    ForcingPresentationCover.Presented env (coreRho root) (root 27) (root 34) (root 35) (root 18) (root 1) (root 37) X x0 p ∧
      HS actionFormula (fun j => env (coreRho root j)) (env (root 34)) (env (coreRho root 6)) (env (root 35)) (env (root 37)) := by
  obtain ⟨_ho,hm0,_hj,hPres0,hG,hFilter,hw,hMu,hI,hD0,_hMergers,_hRow,hc,ht,hLabels0,_hBound,_hObj,hMark0,hCard0,hUncountable,hCoding,hLo,hBit,_hBitSucc,hBits,_rest⟩ := hCore
  have hPres : Presentation (env (coreRho root 0)) (env (root 27)) (env (root 14)) (env (root 3)) (env (root 39))
      (env (coreRho root 1)) (env (coreRho root 2)) (env (coreRho root 3)) (env (coreRho root 4)) (env (coreRho root 5)) (env (coreRho root 6)) := by
    simpa only [coreRho,forcingRho] using hPres0
  have hLabels : ForcingLabelSet.LabelSet (env (coreRho root 6)) (env (root 27)) (env (root 14)) (env (root 36)) (env (root 1)) (env (root 2)) (env (root 37)) := by
    simpa only [coreRho,forcingRho] using hLabels0
  have hNormal := ForcingNormalFilter.is_normal hM hw hMu hG hFilter
  have hSmall := (ForcingSupportSize.native_small hM (env (root 39)) (env (root 13))).mpr hMu.2
  have hA := (ForcingLabelSet.HS_and_fixed hM (fun j => env (coreRho root j)) hPres hG hNormal hFilter hw hSmall hc ht hLabels).1
  refine ⟨?_,hA⟩
  apply ForcingPresentationCover.ordinal_presentation hM hChoice env (coreRho root)
    (root 39) (root 13) (root 27) (root 14) (root 3) (root 34) (root 35) (root 18) (root 19) (root 20) (root 1)
    (root 14) (root 36) (root 1) (root 2) X x0 (root 37) hw hMu hI
    (by simpa only [coreRho,forcingRho] using hD0) (by simpa only [coreRho,forcingRho] using hCard0)
    (by simpa only [coreRho,forcingRho] using hm0) (by simpa only [coreRho,forcingRho] using hMark0)
    hPres hG hFilter hUncountable hCoding ht hLo hBit hBits hX hX0 hLabels hA hp hx0


/-- The nonempty branch of the pinned Main proof. Every ordinal, check,
Cartesian domain, presentation map and parent support is ACTUALLY produced
by the existing constructors before invoking presentation_reverse_injection. -/
private theorem nonempty_on_core (hM : FirstOrder.Theory.Models M nativeZF)
    (hOrder : Project.Gw_order_d (InnerModel.Js_lt_d (M := Project.FirstOrderSemantics.reduct M)))
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) {k : Nat}
    (env : Fin k → M.Carrier .set) (root : Fin 40 → Fin k) (f X Y x0 : Fin k)
    (hCore : ForcingConcreteSystem.Core hM (fun j => env (root j)))
    (hfHS : HS actionFormula (fun j => env (coreRho root j)) (env (root 34)) (env (coreRho root 6)) (env (root 35)) (env f))
    (hX : HS actionFormula (fun j => env (coreRho root j)) (env (root 34)) (env (coreRho root 6)) (env (root 35)) (env X))
    (hY : HS actionFormula (fun j => env (coreRho root j)) (env (root 34)) (env (coreRho root 6)) (env (root 35)) (env Y))
    (hX0 : HS actionFormula (fun j => env (coreRho root j)) (env (root 34)) (env (coreRho root 6)) (env (root 35)) (env x0))
    {p : M.Carrier .set} (hp : (Project.FirstOrderSemantics.reduct M).mem p (env (coreRho root 6)))
    (hf : MapForce env (coreRho root) (root 34) (root 35) (root 18) (env f) (env X) (env Y) p (Source.SetLanguage.surjection 0 1 2))
    (hx0 : Forces false (orderFormula (coreRho root 0) (root 18)) env (env (coreRho root 6)) (env x0) (env X) p) :
    ForcingWellorderedTarget.Result env (coreRho root) (root 34) (root 35) (root 18) (env X) (env Y) p := by
  obtain ⟨hPresented,hA⟩ := present_on_core hM hChoice env root X x0 hCore hX hX0 hp hx0
  obtain ⟨eta,family,hEta,S0,checked,Cart,smap,_hS0,_hS0F,_hTuple0,hChecked,hCart,hCartHS,_hCartFix,hSmapHS,_hSmapFix,hSmapForce⟩ := hPresented
  have hCoreSaved := hCore
  obtain ⟨_ho,hm0,_hj,hPres0,hG,hFilter,hw,hMu,_rest⟩ := hCoreSaved
  have hPres : Presentation (env (coreRho root 0)) (env (root 27)) (env (root 14)) (env (root 3)) (env (root 39))
      (env (coreRho root 1)) (env (coreRho root 2)) (env (coreRho root 3)) (env (coreRho root 4)) (env (coreRho root 5)) (env (coreRho root 6)) := by
    simpa only [coreRho,forcingRho] using hPres0
  have hNormal := ForcingNormalFilter.is_normal hM hw hMu hG hFilter
  let epres : Fin (k+2) → M.Carrier .set := Fin.cases family (Fin.cases eta env)
  let ecart : Fin (k+4) → M.Carrier .set := Fin.cases S0 (Fin.cases checked epres)
  let old : Fin k → Fin (k+4) := fun j => j.succ.succ.succ.succ
  let etaOld : Fin (k+4) := (0 : Fin (k+1)).succ.succ.succ
  let checkOld : Fin (k+4) := (0 : Fin (k+3)).succ
  have heOld (j : Fin k) : ecart (old j) = env j := rfl
  have hOneCart : (1 : Fin (k+4)) = checkOld := by
    apply Fin.ext
    change 1 % (k+4) = 0 % (k+3) + 1
    rw [Nat.mod_eq_of_lt (by omega : 1 < k+4),Nat.mod_eq_of_lt (by omega : 0 < k+3)]
  have hOneEta : (1 : Fin (k+2)) = (0 : Fin (k+1)).succ := by
    apply Fin.ext
    change 1 % (k+2) = 0 % (k+1) + 1
    rw [Nat.mod_eq_of_lt (by omega : 1 < k+2),Nat.mod_eq_of_lt (by omega : 0 < k+1)]
  have hCart0 : ForcingRelationGraph.Graph (orderFormula (old (coreRho root 0)) (old (root 18))) ForcingCompletionGraph.trueRelation
      ecart (old (coreRho root 6)) (old (root 1)) (old (root 37)) checkOld Cart := by
    simpa only [ecart,epres,old,hOneCart] using hCart
  have hCartHS0 : HS actionFormula (fun j => env (coreRho root j)) (env (root 34)) (env (coreRho root 6)) (env (root 35)) Cart := by
    simpa only [Fin.cases_succ] using hCartHS
  have hSmapHS0 : HS actionFormula (fun j => env (coreRho root j)) (env (root 34)) (env (coreRho root 6)) (env (root 35)) smap := by
    simpa only [Fin.cases_succ] using hSmapHS
  have hChecked0 : ForcingCheckName.Checked (env (root 1)) eta checked := by
    simpa only [hOneEta,Fin.cases_succ,Fin.cases_zero] using hChecked
  have hSmapForce0 : MapForce env (coreRho root) (root 34) (root 35) (root 18) smap Cart (env X) p (Source.SetLanguage.surjection 0 1 2) := by
    apply (force_reindex env epres (fun j => j.succ.succ) (fun _ => rfl) (coreRho root) (root 34) (root 35) (root 18)
      (Source.SetLanguage.surjection 0 1 2) (args3 smap Cart (env X)) p).mpr
    simpa only [epres,Fin.cases_succ] using hSmapForce
  let names := ForcingMapCalculus.five (env f) smap (env (root 37)) (env X) (env Y)
  have hNames (j : Fin 5) : HS actionFormula (fun a => env (coreRho root a)) (env (root 34)) (env (coreRho root 6)) (env (root 35)) (names j) := by
    exact Fin.cases hfHS (Fin.cases hSmapHS0 (Fin.cases hA (Fin.cases hX (Fin.cases hY (fun t => Fin.elim0 t))))) j
  obtain ⟨parentS,hS,hSF,hTuple⟩ := ForcingTupleStabilizer.exists_tuple hM (fun j => env (coreRho root j)) hPres hG hNormal names hNames
  let e : Fin (k+7) → M.Carrier .set := Fin.lastCases parentS (Fin.lastCases Cart (Fin.lastCases smap ecart))
  let bind : Fin (k+4) → Fin (k+7) := fun j => j.castSucc.castSucc.castSucc
  let up : Fin k → Fin (k+7) := fun j => bind (old j)
  let rootNew : Fin 40 → Fin (k+7) := fun j => up (root j)
  let Sm : Fin (k+7) := (Fin.last (k+4)).castSucc.castSucc
  let Ct : Fin (k+7) := (Fin.last (k+5)).castSucc
  let Sp : Fin (k+7) := Fin.last (k+6)
  have heBind (j : Fin (k+4)) : e (bind j) = ecart j := by simp only [e,bind,Fin.lastCases_castSucc]
  have he (j : Fin k) : e (up j) = env j := (heBind (old j)).trans (heOld j)
  have es : e Sm = smap := by simp only [e,Sm,Fin.lastCases_castSucc,Fin.lastCases_last]
  have eC : e Ct = Cart := by simp only [e,Ct,Fin.lastCases_castSucc,Fin.lastCases_last]
  have eS : e Sp = parentS := by simp only [e,Sp,Fin.lastCases_last]
  have eEta : e (bind etaOld) = eta := by rw [heBind]; rfl
  have eCheck : e (bind checkOld) = checked := by rw [heBind]; rfl
  have hCoreNew : ForcingConcreteSystem.Core hM (fun j => e (rootNew j)) := by simpa only [rootNew,he] using hCore
  have hVector (j : Fin 5) : e (ForcingMapCalculus.five (up f) Sm (up (root 37)) (up X) (up Y) j) = names j :=
    Fin.cases (he f) (Fin.cases es (Fin.cases (he (root 37)) (Fin.cases (he X) (Fin.cases (he Y) (fun t => Fin.elim0 t))))) j
  have hNamesNew (j : Fin 5) : HS actionFormula (fun a => e (coreRho rootNew a)) (e (rootNew 34)) (e (coreRho rootNew 6)) (e (rootNew 35))
      (e (ForcingMapCalculus.five (up f) Sm (rootNew 37) (up X) (up Y) j)) := by
    simpa only [rootNew,coreRho,he,hVector] using hNames j
  have hFixedNew (j : Fin 5) : Supported (fun a => e (coreRho rootNew a)) (e Sp)
      (e (ForcingMapCalculus.five (up f) Sm (rootNew 37) (up X) (up Y) j)) := by
    intro pi hpi act hAct
    have hFix := ForcingTupleStabilizer.fixed_action hM hTuple (by simpa only [eS] using hpi)
      (by simpa only [rootNew,coreRho,he] using hAct) j
    simpa only [rootNew,coreRho,he,hVector] using hFix
  have hCartNew : ForcingRelationGraph.Graph (orderFormula (coreRho rootNew 0) (rootNew 18)) ForcingCompletionGraph.trueRelation
      e (coreRho rootNew 6) (rootNew 1) (rootNew 37) (bind checkOld) (e Ct) := by
    rw [eC]
    apply ForcingSliceCandidate.graph_transport ecart e (old (coreRho root 6)) (old (root 1)) (old (root 37)) checkOld
      (coreRho rootNew 6) (rootNew 1) (rootNew 37) (bind checkOld)
      (by simpa only [rootNew,coreRho,up] using heBind (old (coreRho root 6)))
      (by simpa only [rootNew,up] using heBind (old (root 1)))
      (by simpa only [rootNew,up] using heBind (old (root 37))) (heBind checkOld) ?_ ?_ hCart0
    · intro a b
      simp only [orderFormula_semantics,rootNew,coreRho,up,heBind]
    · intro q x y
      simp only [ForcingRelationGraphForcing.Holds,ForcingCompletionGraph.trueRelation,Formula.Realize]
  obtain ⟨q,hq,hqp,J,hJ,hForce⟩ := ForcingSlicePresentation.presentation_reverse_injection hM hOrder hChoice e rootNew
    Sp (up f) Sm (up X) (up Y) (bind etaOld) (bind checkOld) Ct hCoreNew
    (by simpa only [rootNew,he,eS] using hS) (by simpa only [rootNew,he,eS] using hSF)
    (by rw [eEta]; exact ordinal_raw hM hEta) hNamesNew hFixedNew
    (by simpa only [rootNew,he,eEta,eCheck] using hChecked0) hCartNew
    (by simpa only [rootNew,coreRho,he] using hp)
    (by
      change MapForce e (coreRho rootNew) (rootNew 34) (rootNew 35) (rootNew 18) (e Sm) (e Ct) (e (up X)) p (Source.SetLanguage.surjection 0 1 2)
      simpa only [MapForce,rootNew,coreRho,he,es,eC] using (force_reindex env e up he (coreRho root) (root 34) (root 35) (root 18)
        (Source.SetLanguage.surjection 0 1 2) (args3 smap Cart (env X)) p).mp hSmapForce0)
    (by
      change MapForce e (coreRho rootNew) (rootNew 34) (rootNew 35) (rootNew 18) (e (up f)) (e (up X)) (e (up Y)) p (Source.SetLanguage.surjection 0 1 2)
      simpa only [MapForce,rootNew,coreRho,he] using (force_reindex env e up he (coreRho root) (root 34) (root 35) (root 18)
        (Source.SetLanguage.surjection 0 1 2) (args3 (env f) (env X) (env Y)) p).mp hf)
  refine ⟨q,?_,?_,J,?_,?_⟩
  · simpa only [rootNew,coreRho,he] using hq
  · simpa only [orderFormula_semantics,rootNew,coreRho,he] using hqp
  · simpa only [rootNew,coreRho,he] using hJ
  · apply (force_reindex env e up he (coreRho root) (root 34) (root 35) (root 18) (Source.SetLanguage.injection 0 1 2) (args3 J (env Y) (env X)) q).mpr
    simpa only [rootNew,coreRho,he] using hForce

/-- Full pinned Main.reverse_injection_dense, including the empty branch.
All original internal sets/HS names/conditions are retained. -/
theorem reverse_injection_dense (hM : FirstOrder.Theory.Models M nativeZF)
    (hOrder : Project.Gw_order_d (InnerModel.Js_lt_d (M := Project.FirstOrderSemantics.reduct M)))
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) {k : Nat}
    (env : Fin k → M.Carrier .set) (root : Fin 40 → Fin k) (f X Y : Fin k)
    (hCore : ForcingConcreteSystem.Core hM (fun j => env (root j)))
    (hfHS : HS actionFormula (fun j => env (coreRho root j)) (env (root 34)) (env (coreRho root 6)) (env (root 35)) (env f))
    (hX : HS actionFormula (fun j => env (coreRho root j)) (env (root 34)) (env (coreRho root 6)) (env (root 35)) (env X))
    (hY : HS actionFormula (fun j => env (coreRho root j)) (env (root 34)) (env (coreRho root 6)) (env (root 35)) (env Y))
    {p : M.Carrier .set} (hp : (Project.FirstOrderSemantics.reduct M).mem p (env (coreRho root 6)))
    (hf : MapForce env (coreRho root) (root 34) (root 35) (root 18) (env f) (env X) (env Y) p (Source.SetLanguage.surjection 0 1 2)) :
    ForcingWellorderedTarget.Result env (coreRho root) (root 34) (root 35) (root 18) (env X) (env Y) p := by
  classical
  have hCoreSaved := hCore
  obtain ⟨_ho,hm0,_hj,hPres0,hG,hFilter,hw,hMu,_hI,_hD,_hMergers,_hRow,_hc,ht,_rest⟩ := hCoreSaved
  have hPres : Presentation (env (coreRho root 0)) (env (root 27)) (env (root 14)) (env (root 3)) (env (root 39))
      (env (coreRho root 1)) (env (coreRho root 2)) (env (coreRho root 3)) (env (coreRho root 4)) (env (coreRho root 5)) (env (coreRho root 6)) := by
    simpa only [coreRho,forcingRho] using hPres0
  have hm : ForcingDiagramPoset.LeftCancelMonoid (env (coreRho root 0)) (env (root 18)) (env (root 19)) := by
    simpa only [coreRho,forcingRho] using hm0
  have hNormal := ForcingNormalFilter.is_normal hM hw hMu hG hFilter
  have hpre := ForcingProductPoset.preorder env (coreRho root 0) (root 18) (coreRho root 6) hm
    hPres.2.2.2.2.1 hPres.2.2.2.1 hPres.2.2.2.2.2
  by_cases hne : ∃ q, (Project.FirstOrderSemantics.reduct M).mem q (env (coreRho root 6)) ∧
      MapRel (orderFormula (coreRho root 0) (root 18)) env q p ∧ ∃ x,
      HS actionFormula (fun j => env (coreRho root j)) (env (root 34)) (env (coreRho root 6)) (env (root 35)) x ∧
      Forces false (orderFormula (coreRho root 0) (root 18)) env (env (coreRho root 6)) x (env X) q
  · obtain ⟨q,hq,hqp,x0,hx0,hMem⟩ := hne
    let e : Fin (k+1) → M.Carrier .set := Fin.cases x0 env
    let rr : Fin 40 → Fin (k+1) := fun j => (root j).succ
    have he (j : Fin k) : e j.succ = env j := rfl
    have ex : e (0 : Fin (k+1)) = x0 := rfl
    have hR (a b : M.Carrier .set) : MapRel (orderFormula (coreRho root 0) (root 18)) env a b ↔
        MapRel (orderFormula (coreRho rr 0) (rr 18)) e a b := by simp only [orderFormula_semantics,rr,coreRho,he]
    obtain ⟨r,hr,hrq,J,hJ,hForce⟩ := nonempty_on_core hM hOrder hChoice e rr f.succ X.succ Y.succ 0
      (by simpa only [rr,he] using hCore) (by simpa only [rr,coreRho,he] using hfHS)
      (by simpa only [rr,coreRho,he] using hX) (by simpa only [rr,coreRho,he] using hY)
      (by simpa only [rr,coreRho,he,ex] using hx0) (by simpa only [rr,coreRho,he] using hq)
      (by simpa only [MapForce,rr,coreRho,he] using (force_reindex env e Fin.succ he (coreRho root) (root 34) (root 35) (root 18)
        (Source.SetLanguage.surjection 0 1 2) (args3 (env f) (env X) (env Y)) q).mp (ForcingFormula.mono hM hpre _ _ hp hq hqp hf))
      (by simpa only [rr,coreRho,he,ex] using (ForcingSeparation.atomic_congr hR false (env (coreRho root 6)) x0 (env X) q).mp hMem)
    have hr' : (Project.FirstOrderSemantics.reduct M).mem r (env (coreRho root 6)) := by simpa only [rr,coreRho,he] using hr
    refine ⟨r,hr',hpre.2 r q p hr' hq hp ((hR r q).mpr hrq) hqp,J,?_,?_⟩
    · simpa only [rr,coreRho,he] using hJ
    · apply (force_reindex env e Fin.succ he (coreRho root) (root 34) (root 35) (root 18) (Source.SetLanguage.injection 0 1 2) (args3 J (env Y) (env X)) r).mpr
      simpa only [rr,coreRho,he] using hForce
  · have hEmpty : ForcingEmptyDomain.Empty env (coreRho root) (root 34) (root 35) (root 18) Y p := by
      intro y hy q hq hqp hyY
      obtain ⟨r,hr,hrq,x,hx,hxX,_hApp⟩ := ForcingImageQuotient.surjection_onto_reuse hM hpre hp hf hy hq hqp hyY hq (hpre.1 q hq)
      exact hne ⟨r,hr,hpre.2 r q p hr hq hp hrq hqp,x,(domain_semantics env (coreRho root) (root 34) (root 35) x).mp hx,hxX⟩
    obtain ⟨J,hJ,hForce⟩ := ForcingEmptyDomain.empty_domain_injection hM env (coreRho root) (root 27) (root 14) (root 3) (root 39)
      (root 34) (root 35) (root 18) (root 1) Y X hPres hG hNormal ht hpre hY hX hp hEmpty
    exact ⟨p,hp,hpre.1 p hp,J,hJ,hForce⟩


/-- Pinned Main.forces_PP_of_dense. Pure source forcing logic, with all
existential witnesses and the full original function formulas retained. -/
private theorem force_PP_of_dense (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    {R : Formula (k+2)} {H : Formula (k+1)} {env : Fin k → M.Carrier .set} {P p : M.Carrier .set}
    (hpre : ForcingAtomicBasic.PreorderOn R env P)
    (hp : (Project.FirstOrderSemantics.reduct M).mem p P)
    (hDense : ∀ q f X Y, (Project.FirstOrderSemantics.reduct M).mem q P → Predicate H env f → Predicate H env X → Predicate H env Y →
      Force R H env (args3 f X Y) P q (Source.SetLanguage.surjection 0 1 2) → ∃ r,
        (Project.FirstOrderSemantics.reduct M).mem r P ∧ MapRel R env r q ∧ ∃ J, Predicate H env J ∧
          Force R H env (args3 J Y X) P r (Source.SetLanguage.injection 0 1 2)) :
    Force R H env Fin.elim0 P p Source.SetLanguage.PP := by
  rw [Source.SetLanguage.PP]
  apply (ForcingFormula.force_all hM hpre hp _ _).mpr
  intro X hX
  apply (ForcingFormula.force_all hM hpre hp _ _).mpr
  intro Y hY
  let v : Fin 2 → M.Carrier .set := Fin.lastCases Y (Fin.lastCases X Fin.elim0)
  change Force R H env v P p ((Formula.ex (Source.SetLanguage.surjection 2 0 1)).imp (Formula.ex (Source.SetLanguage.injection 2 1 0)))
  apply (ForcingFormula.force_imp hM hpre hp _ _ _).mpr
  intro q hq _hqp hEx
  apply (ForcingFormula.force_ex _ _ _ _ _ _ _).mpr
  intro r hr hrq
  obtain ⟨stage,hstage,hstageR,f,hfHS,hf⟩ := (ForcingFormula.force_ex R H env v P q (Source.SetLanguage.surjection 2 0 1)).mp hEx r hr hrq
  have hfCanon : Force R H env (args3 f X Y) P stage (Source.SetLanguage.surjection 0 1 2) := by
    rw [Source.SetLanguage.surjection,ForcingSound.rename hM hpre _ _ _ _ hstage] at hf ⊢
    have he : (fun j => Fin.lastCases f v (args3 (2 : Fin 3) 0 1 j)) =
        (fun j => args3 f X Y (args3 (0 : Fin 3) 1 2 j)) := by
      funext j
      exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun t => Fin.elim0 t))) j
    rwa [he] at hf
  obtain ⟨t,ht,htStage,J,hJ,hInj⟩ := hDense stage f X Y hstage hfHS hX hY hfCanon
  refine ⟨t,ht,hpre.2 t stage r ht hstage hr htStage hstageR,J,hJ,?_⟩
  rw [Source.SetLanguage.injection,ForcingSound.rename hM hpre _ _ _ _ ht] at hInj ⊢
  have he : (fun j => Fin.lastCases J v (args3 (2 : Fin 3) 1 0 j)) =
      (fun j => args3 J Y X (args3 (0 : Fin 3) 1 2 j)) := by
    funext j
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun t => Fin.elim0 t))) j
  rw [he]
  exact hInj

/-- Actual Main.forces_PP on the SAME Core. The dense reverse-injection
input is discharged by the complete all-set theorem above; no oracle remains. -/
theorem forces_PP (hM : FirstOrder.Theory.Models M nativeZF)
    (hOrder : Project.Gw_order_d (InnerModel.Js_lt_d (M := Project.FirstOrderSemantics.reduct M)))
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) {k : Nat}
    (env : Fin k → M.Carrier .set) (root : Fin 40 → Fin k)
    (hCore : ForcingConcreteSystem.Core hM (fun j => env (root j)))
    {p : M.Carrier .set} (hp : (Project.FirstOrderSemantics.reduct M).mem p (env (coreRho root 6))) :
    Force (orderFormula (coreRho root 0) (root 18)) (domain (coreRho root) (root 34) (root 35)) env Fin.elim0
      (env (coreRho root 6)) p Source.SetLanguage.PP := by
  have hCoreSaved := hCore
  obtain ⟨_ho,hm0,_hj,hPres0,_hG,_hF,_rest⟩ := hCoreSaved
  have hPres : Presentation (env (coreRho root 0)) (env (root 27)) (env (root 14)) (env (root 3)) (env (root 39))
      (env (coreRho root 1)) (env (coreRho root 2)) (env (coreRho root 3)) (env (coreRho root 4)) (env (coreRho root 5)) (env (coreRho root 6)) := by
    simpa only [coreRho,forcingRho] using hPres0
  have hm : ForcingDiagramPoset.LeftCancelMonoid (env (coreRho root 0)) (env (root 18)) (env (root 19)) := by
    simpa only [coreRho,forcingRho] using hm0
  have hpre := ForcingProductPoset.preorder env (coreRho root 0) (root 18) (coreRho root 6) hm
    hPres.2.2.2.2.1 hPres.2.2.2.1 hPres.2.2.2.2.2
  apply force_PP_of_dense hM hpre hp
  intro q f X Y hq hfHS hX hY hf
  let e : Fin (k+3) → M.Carrier .set := Fin.lastCases f (Fin.lastCases Y (Fin.lastCases X env))
  let up : Fin k → Fin (k+3) := fun j => j.castSucc.castSucc.castSucc
  let rootNew : Fin 40 → Fin (k+3) := fun j => up (root j)
  let fi : Fin (k+3) := Fin.last (k+2)
  let xi : Fin (k+3) := (Fin.last k).castSucc.castSucc
  let yi : Fin (k+3) := (Fin.last (k+1)).castSucc
  have he (j : Fin k) : e (up j) = env j := by simp only [e,up,Fin.lastCases_castSucc]
  have ef : e fi = f := by simp only [e,fi,Fin.lastCases_last]
  have ex : e xi = X := by simp only [e,xi,Fin.lastCases_castSucc,Fin.lastCases_last]
  have ey : e yi = Y := by simp only [e,yi,Fin.lastCases_castSucc,Fin.lastCases_last]
  obtain ⟨r,hr,hrq,J,hJ,hForce⟩ := reverse_injection_dense hM hOrder hChoice e rootNew fi xi yi
    (by simpa only [rootNew,he] using hCore)
    (by simpa only [rootNew,coreRho,he,ef] using (domain_semantics env (coreRho root) (root 34) (root 35) f).mp hfHS)
    (by simpa only [rootNew,coreRho,he,ex] using (domain_semantics env (coreRho root) (root 34) (root 35) X).mp hX)
    (by simpa only [rootNew,coreRho,he,ey] using (domain_semantics env (coreRho root) (root 34) (root 35) Y).mp hY)
    (by simpa only [rootNew,coreRho,he] using hq)
    (by simpa only [MapForce,rootNew,coreRho,he,ef,ex,ey] using (force_reindex env e up he (coreRho root) (root 34) (root 35) (root 18)
      (Source.SetLanguage.surjection 0 1 2) (args3 f X Y) q).mp hf)
  refine ⟨r,?_,?_,J,?_,?_⟩
  · simpa only [rootNew,coreRho,he] using hr
  · simpa only [orderFormula_semantics,rootNew,coreRho,he] using hrq
  · apply (domain_semantics env (coreRho root) (root 34) (root 35) J).mpr
    simpa only [rootNew,coreRho,he] using hJ
  · apply (force_reindex env e up he (coreRho root) (root 34) (root 35) (root 18) (Source.SetLanguage.injection 0 1 2) (args3 J Y X) r).mpr
    simpa only [rootNew,coreRho,he,ex,ey] using hForce

private theorem core_renamed_semantics (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Env (Project.FirstOrderSemantics.reduct M) k) (root : Fin 40 → Fin k) :
    Project.Formula.satisfies env (ForcingConcreteSystem.coreFormula.rename root) ↔
      ForcingConcreteSystem.Core hM (fun j => env.bound (root j)) := by
  rw [Project.Formula.satisfies_rename]
  exact ForcingConcreteSystem.coreFormula_semantics hM _

private theorem args3_map {k : Nat} (env : Fin k → M.Carrier .set) (f X Y : Fin k) :
    (fun j => env (args3 f X Y j)) = args3 (env f) (env X) (env Y) := by
  funext j
  exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun t => Fin.elim0 t))) j

/-- Same actual Core proves PP at every condition, without assuming the
existence of a surjection. The second conjunct records full all-set density. -/
def sentence {k : Nat} (root : Fin 40 → Fin k) (f X Y p : Fin k) : Project.Sentence where
  formula :=
    let rho := coreRho root
    Project.Formula.forallClosure k
      ((ForcingConcreteSystem.coreFormula.rename root).imp
        ((Definitional.Formula.mem (.bound p) (.bound (rho 6))).imp
          (.conj
            (ProjectSyntax.encode id (ForcingFormula.formula (orderFormula (rho 0) (root 18)) (domain rho (root 34) (root 35)) id
              Fin.elim0 (rho 6) p Source.SetLanguage.PP))
            ([ProjectSyntax.encode id (ForcingHS.hs actionFormula rho (root 34) (rho 6) (root 35) f),
              ProjectSyntax.encode id (ForcingHS.hs actionFormula rho (root 34) (rho 6) (root 35) X),
              ProjectSyntax.encode id (ForcingHS.hs actionFormula rho (root 34) (rho 6) (root 35) Y),
              ProjectSyntax.encode id (ForcingFormula.formula (orderFormula (rho 0) (root 18)) (domain rho (root 34) (root 35)) id
                (args3 f X Y) (rho 6) p (Source.SetLanguage.surjection 0 1 2))].foldr Definitional.Formula.imp
              (ProjectSyntax.encode id (ForcingWellorderedTarget.resultFormula rho (root 34) (root 35) (root 18) X Y p))))))
  freeClosed := by
    simp -implicitDefEqProofs [List.foldr,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
      Definitional.Formula.freeClosed_rename,ForcingConcreteSystem.coreFormula_freeClosed]

theorem models {k : Nat} (root : Fin 40 → Fin k) (f X Y p : Fin k)
    (hM : FirstOrder.Theory.Models M nativeZF)
    (hOrder : Project.Gw_order_d (InnerModel.Js_lt_d (M := Project.FirstOrderSemantics.reduct M)))
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) :
    (Project.fo_sentence (sentence root f X Y p)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM),SetTheory.Structure.satisfiesSentence_iff]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro env
  simp only [List.foldr,Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,core_renamed_semantics hM,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ForcingHS.hs_semantics,
    ForcingFormula.formula_semantics,ForcingWellorderedTarget.resultFormula_semantics,id_eq,args3_map]
  intro hCore hp
  constructor
  · exact forces_PP hM hOrder hChoice env root hCore hp
  · intro hfHS hXHS hYHS hf
    exact reverse_injection_dense hM hOrder hChoice env root f X Y hCore hfHS hXHS hYHS hp hf

/-- Ordinary nativeZF original-kernel derivation. The SAME completed L
interpretation discharges both background Choice and the L-order; neither
is an added external assumption of this object theorem. -/
theorem kernel_certificate {k : Nat} (root : Fin 40 → Fin k) (f X Y p : Fin k) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (ConstructibleGround.relative
      (sentence root f X Y p))) := by
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
    (models root f X Y p hL (ConstructionRoundSelection.l_order hN) hChoice)

end PPAC.Migration.ForcingReverseInjection
