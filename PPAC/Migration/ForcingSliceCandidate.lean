/- Pinned SliceAssembly.slice_candidate:118-156. Actual pointwise source
construction on the SAME completed Core. Reuse full slice/part surjections,
wellorderable-target injection and BOTH nonwellorderable-image bijections.
Existing raw compose/inverse operations are reused through public interfaces. -/
import PPAC.Migration.ForcingEmptyDomain
import PPAC.Migration.ForcingSliceParameters
import PPAC.Migration.ForcingRootProbes
import PPAC.Migration.ForcingNonwellorderableImage

namespace PPAC.Migration.ForcingSliceCandidate
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open Source (Formula)
open Source.SetLanguage (args1 args2 args3)
open ForcingMapConditions (MapRel)
open ForcingAtomicRelations (Forces)
open ForcingFormula (Force)
open ForcingProductFamily (Presentation actionFormula)
open ForcingProductSymmetry (orderFormula)
open ForcingHS (HS)
open ForcingPairUnion (domain domain_semantics)
open ForcingConcreteSystem (forcingRho)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 400000
universe u v
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

private abbrev MapForce {k : Nat} (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k)
    (G F mul : Fin k) (f X Y p : M.Carrier .set) (phi : Formula 3) : Prop :=
  Force (orderFormula (rho 0) mul) (domain rho G F) env (args3 f X Y) (env (rho 6)) p phi

open ForcingNonwellorderableImage (force_reindex pre_reindex compose inverse)

private abbrev coreRho {k : Nat} (root : Fin 40 → Fin k) : Fin 7 → Fin k := fun j => root (forcingRho j)

private theorem coreRho_last {k : Nat} (root : Fin 40 → Fin k) : coreRho root 6 = root 33 := by
  rfl

theorem unary_reindex {k l n : Nat} (env : Fin k → M.Carrier .set) (other : Fin l → M.Carrier .set)
    (base : Fin k → Fin l) (he : ∀ j, other (base j) = env j) (rho : Fin 7 → Fin k)
    (G F mul : Fin k) (names : Fin n → Fin k) (phi : Formula (n+1)) (p x : M.Carrier .set) :
    MapRel (ForcingSliceGeometry.unaryOf rho G F mul names phi) env p x ↔
      MapRel (ForcingSliceGeometry.unaryOf (fun j => base (rho j)) (base G) (base F) (base mul)
        (fun j => base (names j)) phi) other p x := by
  rw [ForcingSliceGeometry.unaryOf_semantics,ForcingSliceGeometry.unaryOf_semantics]
  have hv : (fun j => other (base (names j))) = (fun j => env (names j)) := funext (fun j => he (names j))
  rw [hv,he]
  apply ForcingSeparation.force_congr ?_ ?_ phi _ _ _
  · intro a b
    simp only [ForcingProductSymmetry.orderFormula_semantics,he]
  · intro a
    simp only [domain_semantics,he]

theorem four_map {a : Type v} {b : Type u} (g : a → b) (s A X ci : a) :
    (fun j => g (ForcingSliceGeometry.four s A X ci j)) = ForcingSliceGeometry.four (g s) (g A) (g X) (g ci) := by
  funext j
  exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun t => Fin.elim0 t)))) j

theorem selected_transport {k l : Nat} {R Q : Formula (k+2)} {R' Q' : Formula (l+2)}
    {env : Fin k → M.Carrier .set} {other : Fin l → M.Carrier .set}
    (hR : ∀ a b, MapRel R env a b ↔ MapRel R' other a b)
    (hQ : ∀ a b, MapRel Q env a b ↔ MapRel Q' other a b)
    {P X name : M.Carrier .set} (hName : ForcingSliceSelection.Selected R Q env P X name) :
    ForcingSliceSelection.Selected R' Q' other P X name := by
  intro child p
  exact (hName child p).trans (and_congr Iff.rfl (and_congr Iff.rfl
    (and_congr (ForcingSeparation.atomic_congr hR false P child X p) (hQ p child))))

theorem separated_transport {k l n : Nat} {R : Formula (k+2)} {H : Formula (k+1)}
    {R' : Formula (l+2)} {H' : Formula (l+1)}
    {env : Fin k → M.Carrier .set} {other : Fin l → M.Carrier .set}
    (hR : ∀ a b, MapRel R env a b ↔ MapRel R' other a b)
    (hH : ∀ a, ForcingClassEvaluation.Predicate H env a ↔ ForcingClassEvaluation.Predicate H' other a)
    {P X name : M.Carrier .set} {v : Fin n → M.Carrier .set} {phi : Formula (n+1)}
    (hName : ForcingSeparation.Separated R H env v P X name phi) :
    ForcingSeparation.Separated R' H' other v P X name phi := by
  intro child p
  exact (hName child p).trans (and_congr Iff.rfl (and_congr Iff.rfl
    (and_congr (ForcingSeparation.atomic_congr hR false P child X p)
      (ForcingSeparation.force_congr hR hH phi (Fin.lastCases child v) P p))))

/-- Keep the SAME literal collected graph and its existing product-entry
family. Only equivalent R/Q tests and parameter coordinates change. -/
theorem graph_transport {k l : Nat} {R : Formula (k+2)} {Q : Formula (k+3)}
    {R' : Formula (l+2)} {Q' : Formula (l+3)}
    (env : Fin k → M.Carrier .set) (other : Fin l → M.Carrier .set)
    (P t X Y : Fin k) (P' t' X' Y' : Fin l)
    (hP : other P' = env P) (ht : other t' = env t) (hX : other X' = env X) (hY : other Y' = env Y)
    (hR : ∀ a b, MapRel R env a b ↔ MapRel R' other a b)
    (hQ : ∀ p x y, ForcingRelationGraphForcing.Holds Q env p x y ↔ ForcingRelationGraphForcing.Holds Q' other p x y)
    {name : M.Carrier .set} (hGraph : ForcingRelationGraph.Graph R Q env P t X Y name) :
    ForcingRelationGraph.Graph R' Q' other P' t' X' Y' name := by
  obtain ⟨J,f,hJ,hf,hCollected⟩ := hGraph
  refine ⟨J,f,?_,?_,?_⟩
  · simpa only [hX,hY] using hJ
  · simpa only [ht] using hf
  · have hTest (i p : M.Carrier .set) :
        ForcingRelationGraph.Test R Q env (env P) (env X) (env Y) i p ↔
          ForcingRelationGraph.Test R' Q' other (env P) (env X) (env Y) i p := by
      unfold ForcingRelationGraph.Test
      apply exists_congr; intro a
      apply exists_congr; intro b
      apply exists_congr; intro x
      apply exists_congr; intro c
      apply exists_congr; intro y
      apply exists_congr; intro d
      refine and_congr Iff.rfl (and_congr Iff.rfl (and_congr Iff.rfl
        (and_congr (ForcingSeparation.atomic_congr hR false (env P) x (env X) p)
          (and_congr (ForcingSeparation.atomic_congr hR false (env P) y (env Y) p) ?_))))
      exact hQ p x y
    intro z
    refine (hCollected z).trans ?_
    simp only [ForcingCollectedName.Entry,ForcingCollectedName.Admissible,
      ForcingRelationGraph.testFormula_semantics,hP,hX,hY,hTest]

section ExtraOperations
variable {k : Nat} (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k)
variable (I K two w G F mul top : Fin k) (hM : FirstOrder.Theory.Models M nativeZF)
variable (hp : Presentation (env (rho 0)) (env I) (env K) (env two) (env w)
  (env (rho 1)) (env (rho 2)) (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
variable (hG : ForcingLabelPermutations.Carrier (env I) (env G))
variable (hF : ForcingNormalFilter.Normal (env I) (env G) (env F))
variable (ht : ForcingWithTopCarrier.Empty (env top))
variable (hpre : ForcingAtomicBasic.PreorderOn (orderFormula (rho 0) mul) env (env (rho 6)))
include hM hp hG hF ht hpre

/-- Instantiate the EXISTING full wellorderable_image at the actual raw
partGraph and its two actual piece names; no new wellorder construction. -/
private theorem image_wellorderable {f X Y p : M.Carrier .set}
    (hf : HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) f)
    (hX : HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) X)
    (hY : HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) Y)
    (hpW : (Project.FirstOrderSemantics.reduct M).mem p (env (rho 6)))
    (hSurj : MapForce env rho G F mul f X Y p (Source.SetLanguage.surjection 0 1 2))
    (hWo : Force (orderFormula (rho 0) mul) (domain rho G F) env (args1 X) (env (rho 6)) p (ForcingCheckOrdinal.wellorderable 0)) :
    Force (orderFormula (rho 0) mul) (domain rho G F) env (args1 Y) (env (rho 6)) p (ForcingCheckOrdinal.wellorderable 0) := by
  let up : Fin k → Fin (k+4) := fun j => j.castSucc.castSucc.castSucc.castSucc
  let rr : Fin 7 → Fin (k+4) := fun j => up (rho j)
  let e : Fin (k+4) → M.Carrier .set := Fin.lastCases p (Fin.lastCases Y (Fin.lastCases X (Fin.lastCases f env)))
  let fi : Fin (k+4) := (Fin.last k).castSucc.castSucc.castSucc
  let xi : Fin (k+4) := (Fin.last (k+1)).castSucc.castSucc
  let yi : Fin (k+4) := (Fin.last (k+2)).castSucc
  let pi : Fin (k+4) := Fin.last (k+3)
  have he (j : Fin k) : e (up j) = env j := by simp only [e,up,Fin.lastCases_castSucc]
  have ef : e fi = f := by simp only [e,fi,Fin.lastCases_last,Fin.lastCases_castSucc]
  have ex : e xi = X := by simp only [e,xi,Fin.lastCases_last,Fin.lastCases_castSucc]
  have ey : e yi = Y := by simp only [e,yi,Fin.lastCases_last,Fin.lastCases_castSucc]
  have ep : e pi = p := by simp only [e,pi,Fin.lastCases_last]
  have hRes := ForcingIndexedImage.wellorderable_image hM e rr (up I) (up K) (up two) (up w)
    (up G) (up F) (up mul) (up top) fi xi yi pi
    (by simpa only [rr,he] using hp) (by simpa only [he] using hG) (by simpa only [he] using hF)
    (by simpa only [he] using ht) (pre_reindex env e up he rho mul hpre)
    (by simpa only [rr,he,ef] using hf) (by simpa only [rr,he,ex] using hX) (by simpa only [rr,he,ey] using hY)
    (by simpa only [rr,he,ep] using hpW)
    (by simpa only [rr,he,ef,ex,ey,ep] using (force_reindex env e up he rho G F mul (Source.SetLanguage.surjection 0 1 2) (args3 f X Y) p).mp hSurj)
    (by simpa only [rr,he,ex,ep] using (force_reindex env e up he rho G F mul (ForcingCheckOrdinal.wellorderable 0) (args1 X) p).mp hWo)
  apply (force_reindex env e up he rho G F mul (ForcingCheckOrdinal.wellorderable 0) (args1 Y) p).mpr
  simpa only [rr,he,ey,ep] using hRes

/-- Use the accepted source nonwellorderable_member_dense at one raw
piece name. The actual default is chosen only below this one condition. -/
private theorem member_raw {X p : M.Carrier .set}
    (hX : HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) X)
    (hpW : (Project.FirstOrderSemantics.reduct M).mem p (env (rho 6)))
    (hNon : Force (orderFormula (rho 0) mul) (domain rho G F) env (args1 X)
      (env (rho 6)) p (ForcingCheckOrdinal.wellorderable 0).neg) :
    ∃ q, (Project.FirstOrderSemantics.reduct M).mem q (env (rho 6)) ∧
      MapRel (orderFormula (rho 0) mul) env q p ∧ ∃ d,
      HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) d ∧
      Forces false (orderFormula (rho 0) mul) env (env (rho 6)) d X q := by
  let e : Fin (k+1) → M.Carrier .set := Fin.cases X env
  let rr : Fin 7 → Fin (k+1) := fun j => (rho j).succ
  have he (j : Fin k) : e j.succ = env j := rfl
  have hx : e (0 : Fin (k+1)) = X := rfl
  have hpre' := pre_reindex env e Fin.succ he rho mul hpre
  obtain ⟨q,hq,hqp,d,hd,hMem⟩ := ForcingEmptyDomain.nonwellorderable_member_dense hM e rr
    I.succ K.succ two.succ w.succ G.succ F.succ mul.succ top.succ 0
    (by simpa only [rr,he] using hp) (by simpa only [he] using hG) (by simpa only [he] using hF)
    (by simpa only [he] using ht) hpre' (by simpa only [rr,he,hx] using hX)
    (by simpa only [rr,he] using hpW)
    (by simpa only [rr,he,hx] using (force_reindex env e Fin.succ he rho G F mul
      (ForcingCheckOrdinal.wellorderable 0).neg (args1 X) p).mp hNon)
    p (by simpa only [rr,he] using hpW) (hpre'.1 p (by simpa only [rr,he] using hpW))
  have hR (a b : M.Carrier .set) : MapRel (orderFormula (rho 0) mul) env a b ↔
      MapRel (orderFormula (rr 0) mul.succ) e a b := by simp only [ForcingProductSymmetry.orderFormula_semantics,rr,he]
  refine ⟨q,?_,(hR q p).mpr hqp,d,?_,?_⟩
  · simpa only [rr,he] using hq
  · simpa only [rr,he] using (domain_semantics e rr G.succ F.succ d).mp hd
  · apply (ForcingSeparation.atomic_congr hR false (env (rho 6)) d X q).mpr
    simpa only [rr,he,hx] using hMem

/-- Full source subset_image_surjection, at ACTUAL raw names and the ONE
explicit default obtained below ONE condition. Reuse actual_reuse and the
already accepted graph_surjection; no uniform choice of defaults. -/
private theorem subset_surjection {f A target D d p : M.Carrier .set}
    (hf : HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) f)
    (hA : HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) A)
    (hD : HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) D)
    (hd : HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) d)
    (hpW : (Project.FirstOrderSemantics.reduct M).mem p (env (rho 6)))
    (hSurj : MapForce env rho G F mul f A target p (Source.SetLanguage.surjection 0 1 2))
    (hSub : ForcingPowerName.SubsetF (orderFormula (rho 0) mul) (domain rho G F) env (env (rho 6)) p D target)
    (hMem : Forces false (orderFormula (rho 0) mul) env (env (rho 6)) d D p) :
    ∃ J, HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) J ∧
      MapForce env rho G F mul J A D p (Source.SetLanguage.surjection 0 1 2) := by
  let up5 : Fin k → Fin (k+5) := fun j => j.castSucc.castSucc.castSucc.castSucc.castSucc
  let rr5 : Fin 7 → Fin (k+5) := fun j => up5 (rho j)
  let extra : Fin (k+5) → M.Carrier .set := Fin.lastCases d (Fin.lastCases D (Fin.lastCases target (Fin.lastCases A (Fin.lastCases f env))))
  let fi : Fin (k+5) := (Fin.last k).castSucc.castSucc.castSucc.castSucc
  let ai : Fin (k+5) := (Fin.last (k+1)).castSucc.castSucc.castSucc
  let ti : Fin (k+5) := (Fin.last (k+2)).castSucc.castSucc
  let di : Fin (k+5) := (Fin.last (k+3)).castSucc
  let dd : Fin (k+5) := Fin.last (k+4)
  have he5 (j : Fin k) : extra (up5 j) = env j := by simp only [extra,up5,Fin.lastCases_castSucc]
  have ef : extra fi = f := by simp only [extra,fi,Fin.lastCases_last,Fin.lastCases_castSucc]
  have ea : extra ai = A := by simp only [extra,ai,Fin.lastCases_last,Fin.lastCases_castSucc]
  have et : extra ti = target := by simp only [extra,ti,Fin.lastCases_last,Fin.lastCases_castSucc]
  have ed : extra di = D := by simp only [extra,di,Fin.lastCases_last,Fin.lastCases_castSucc]
  have edd : extra dd = d := by simp only [extra,dd,Fin.lastCases_last]
  have hNames (j : Fin 4) : HS actionFormula (fun a => extra (rr5 a)) (extra (up5 G)) (extra (rr5 6)) (extra (up5 F))
      (extra (ForcingSubsetImage.four fi ai di dd j)) := by
    have hAll : (fun j => extra (ForcingSubsetImage.four fi ai di dd j)) = ForcingSubsetImage.four f A D d := by
      funext j
      exact Fin.cases ef (Fin.cases ea (Fin.cases ed (Fin.cases edd (fun t => Fin.elim0 t)))) j
    simp only [rr5,he5,congrFun hAll j]
    exact Fin.cases hf (Fin.cases hA (Fin.cases hD (Fin.cases hd (fun t => Fin.elim0 t)))) j
  obtain ⟨S,J,_hS,_hSF,_hTuple,hGraph,hJHS,_hJFix⟩ := ForcingMapCalculus.actual_reuse hM extra rr5
    (up5 I) (up5 K) (up5 two) (up5 w) (up5 G) (up5 F) (up5 mul) (up5 top)
    (ForcingSubsetImage.four fi ai di dd) ForcingSubsetImage.subsetFormula
    (Fin.succ (0 : Fin 3)) (Fin.succ (Fin.succ (0 : Fin 2)))
    (by simpa only [rr5,he5] using hp) (by simpa only [he5] using hG) (by simpa only [he5] using hF)
    (by simpa only [he5] using ht) hNames
  let e : Fin (k+6) → M.Carrier .set := Fin.cases S extra
  let up : Fin k → Fin (k+6) := fun j => (up5 j).succ
  let rr : Fin 7 → Fin (k+6) := fun j => up (rho j)
  have he (j : Fin k) : e (up j) = env j := he5 j
  have ef' : e fi.succ = f := ef
  have ea' : e ai.succ = A := ea
  have et' : e ti.succ = target := et
  have ed' : e di.succ = D := ed
  have edd' : e dd.succ = d := edd
  have hn : (fun j => (ForcingSubsetImage.four fi ai di dd j).succ) = ForcingSubsetImage.four fi.succ ai.succ di.succ dd.succ := by
    funext j
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun t => Fin.elim0 t)))) j
  have hGraph' : ForcingRelationGraph.Graph (orderFormula (rr 0) (up mul))
      (ForcingSubsetImage.relation rr (up G) (up F) (up mul) fi.succ ai.succ di.succ dd.succ)
      e (rr 6) (up top) ai.succ di.succ J := by
    rw [hn] at hGraph
    simpa only [ForcingSubsetImage.relation,ForcingSubsetImage.four,Fin.cases_zero,Fin.cases_succ,rr,up,rr5,e] using hGraph
  have hR (x y : M.Carrier .set) : ForcingMapConditions.MapRel (orderFormula (rho 0) mul) env x y ↔
      ForcingMapConditions.MapRel (orderFormula (rr 0) (up mul)) e x y := by
    simp only [ForcingProductSymmetry.orderFormula_semantics,rr,he]
  have hH (x : M.Carrier .set) : ForcingClassEvaluation.Predicate (domain rho G F) env x ↔
      ForcingClassEvaluation.Predicate (domain rr (up G) (up F)) e x := by simp only [domain_semantics,rr,he]
  have hSub' : ForcingPowerName.SubsetF (orderFormula (rr 0) (up mul)) (domain rr (up G) (up F)) e (e (rr 6)) p (e di.succ) (e ti.succ) := by
    intro x hx q hq hqp hxD
    have hy := hSub x ((hH x).mpr hx) q (by simpa only [rr,he] using hq) ((hR q p).mpr hqp)
      ((ForcingSeparation.atomic_congr hR false (env (rho 6)) x D q).mpr (by simpa only [rr,he,ed'] using hxD))
    simpa only [rr,he,et'] using (ForcingSeparation.atomic_congr hR false (env (rho 6)) x target q).mp hy
  have hForce := ForcingSubsetImage.graph_surjection hM e rr (up I) (up K) (up two) (up w)
    (up G) (up F) (up mul) (up top) fi.succ ai.succ ti.succ di.succ dd.succ
    (by simpa only [rr,he] using hp) (by simpa only [he] using hG) (by simpa only [he] using hF)
    (by simpa only [he] using ht) (pre_reindex env e up he rho mul hpre)
    (by simpa only [rr,he,ea'] using hA) (by simpa only [rr,he,ed'] using hD) (by simpa only [rr,he,edd'] using hd)
    hGraph' (by simpa only [rr,he] using hpW)
    (by simpa only [rr,he,ef',ea',et'] using (force_reindex env e up he rho G F mul (Source.SetLanguage.surjection 0 1 2) (args3 f A target) p).mp hSurj)
    hSub' (by simpa only [rr,he,edd',ed'] using (ForcingSeparation.atomic_congr hR false (env (rho 6)) d D p).mp hMem)
  refine ⟨J,?_,?_⟩
  · simpa only [rr5,he5] using hJHS
  · apply (force_reindex env e up he rho G F mul (Source.SetLanguage.surjection 0 1 2) (args3 J A D) p).mpr
    simpa only [rr,he,ea',ed'] using hForce

end ExtraOperations

/-- The already completed image classification on the SAME Core, transported
only through the existing forcing congruence. No classification oracle. -/
private theorem image_bijection (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (root : Fin 40 → Fin k)
    (hCore : ForcingConcreteSystem.Core hM (fun j => env (root j)))
    (hOutcome : ForcingConcreteSystem.Outcome (fun j => env (root j)))
    {f B p : M.Carrier .set}
    (hf : HS actionFormula (fun j => env (coreRho root j)) (env (root 34)) (env (root 33)) (env (root 35)) f)
    (hB : HS actionFormula (fun j => env (coreRho root j)) (env (root 34)) (env (root 33)) (env (root 35)) B)
    (hp : (Project.FirstOrderSemantics.reduct M).mem p (env (root 33)))
    (hSurj : MapForce env (coreRho root) (root 34) (root 35) (root 18) f (env (root 37)) B p (Source.SetLanguage.surjection 0 1 2))
    (hNon : Force (orderFormula (coreRho root 0) (root 18)) (domain (coreRho root) (root 34) (root 35)) env
      (args1 B) (env (root 33)) p (ForcingCheckOrdinal.wellorderable 0).neg) :
    ∃ q, (Project.FirstOrderSemantics.reduct M).mem q (env (root 33)) ∧
      MapRel (orderFormula (coreRho root 0) (root 18)) env q p ∧ ∃ J,
      HS actionFormula (fun j => env (coreRho root j)) (env (root 34)) (env (root 33)) (env (root 35)) J ∧
      MapForce env (coreRho root) (root 34) (root 35) (root 18) J (env (root 37)) B q
        ((Source.SetLanguage.surjection 0 1 2).conj (Source.SetLanguage.injection 0 1 2)) := by
  let ground : Fin 40 → M.Carrier .set := fun j => env (root j)
  have he (j : Fin 40) : env (root j) = ground j := rfl
  obtain ⟨q,hq,hqp,J,hJ,hForce⟩ := ForcingNonwellorderableImage.on_core hM ground hCore hOutcome f B p hf hB hp
    ((force_reindex ground env root he forcingRho 34 35 18 (Source.SetLanguage.surjection 0 1 2) (args3 f (env (root 37)) B) p).mpr hSurj)
    ((force_reindex ground env root he forcingRho 34 35 18 (ForcingCheckOrdinal.wellorderable 0).neg (args1 B) p).mpr hNon)
  refine ⟨q,hq,?_,J,hJ,?_⟩
  · simpa only [ForcingProductSymmetry.orderFormula_semantics,coreRho,ground] using hqp
  · exact (force_reindex ground env root he forcingRho 34 35 18
      ((Source.SetLanguage.surjection 0 1 2).conj (Source.SetLanguage.injection 0 1 2)) (args3 J (env (root 37)) B) q).mp hForce


/-- Consume the SAME Core's actual probes and cardinal/row background in the
already completed wellorderable_target_injection. Raw names are only bound
into an extended context; the source forcing relation stays unchanged. -/
private theorem wellordered_target (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) {k : Nat}
    (env : Fin k → M.Carrier .set) (root : Fin 40 → Fin k)
    (hCore : ForcingConcreteSystem.Core hM (fun j => env (root j)))
    {f X Y p : M.Carrier .set}
    (hf : HS actionFormula (fun j => env (coreRho root j)) (env (root 34)) (env (root 33)) (env (root 35)) f)
    (hX : HS actionFormula (fun j => env (coreRho root j)) (env (root 34)) (env (root 33)) (env (root 35)) X)
    (hY : HS actionFormula (fun j => env (coreRho root j)) (env (root 34)) (env (root 33)) (env (root 35)) Y)
    (hp : (Project.FirstOrderSemantics.reduct M).mem p (env (root 33)))
    (hSurj : MapForce env (coreRho root) (root 34) (root 35) (root 18) f X Y p (Source.SetLanguage.surjection 0 1 2))
    (hWo : Force (orderFormula (coreRho root 0) (root 18)) (domain (coreRho root) (root 34) (root 35)) env
      (args1 Y) (env (root 33)) p (ForcingCheckOrdinal.wellorderable 0)) :
    ForcingWellorderedTarget.Result env (coreRho root) (root 34) (root 35) (root 18) X Y p := by
  obtain ⟨hProbes,hIndex⟩ := ForcingRootProbes.on_core hM (fun j => env (root j)) hCore
  obtain ⟨_hOrd,hm,_hJoins,hPres,hG,hFilter,hw,hMu,hI,hD,hMergers,hRow,_hc,ht,_hLabels,_hBound,_hObject,hMark,hCard,_rest⟩ := hCore
  let up : Fin k → Fin (k+4) := fun j => j.castSucc.castSucc.castSucc.castSucc
  let rr : Fin 7 → Fin (k+4) := fun j => up (coreRho root j)
  let e : Fin (k+4) → M.Carrier .set := Fin.lastCases p (Fin.lastCases Y (Fin.lastCases X (Fin.lastCases f env)))
  let fi : Fin (k+4) := (Fin.last k).castSucc.castSucc.castSucc
  let xi : Fin (k+4) := (Fin.last (k+1)).castSucc.castSucc
  let yi : Fin (k+4) := (Fin.last (k+2)).castSucc
  let pi : Fin (k+4) := Fin.last (k+3)
  have he (j : Fin k) : e (up j) = env j := by simp only [e,up,Fin.lastCases_castSucc]
  have ef : e fi = f := by simp only [e,fi,Fin.lastCases_last,Fin.lastCases_castSucc]
  have ex : e xi = X := by simp only [e,xi,Fin.lastCases_last,Fin.lastCases_castSucc]
  have ey : e yi = Y := by simp only [e,yi,Fin.lastCases_last,Fin.lastCases_castSucc]
  have ep : e pi = p := by simp only [e,pi,Fin.lastCases_last]
  have hW : e (rr 6) = env (root 33) := by
    dsimp only [rr]
    rw [he,coreRho_last]
  obtain ⟨q,hq,hqp,J,hJ,hForce⟩ := ForcingWellorderedTarget.wellorderable_target_injection hM hChoice e rr
    (up (root 39)) (up (root 13)) (up (root 16)) (up (root 14)) (up (root 19)) (up (root 20))
    (up (root 21)) (up (root 22)) (up (root 23)) (up (root 24)) (up (root 27)) (up (root 14)) (up (root 3))
    (up (root 34)) (up (root 35)) (up (root 18)) (up (root 13)) (up (root 1)) fi xi yi pi
    (by simpa only [he] using hw) (by simpa only [he] using hMu) (by simpa only [he] using hI)
    (by simpa only [rr,he,coreRho_last,coreRho,forcingRho] using hD) (by simpa only [rr,he,coreRho_last,coreRho,forcingRho] using hCard)
    (by simpa only [he] using hMergers) (by simpa only [rr,he,coreRho_last,coreRho,forcingRho] using hRow)
    (by simpa only [rr,he,coreRho_last,coreRho,forcingRho] using hm) (by simpa only [rr,he,coreRho_last,coreRho,forcingRho] using hPres)
    (by simpa only [he] using hG) (by simpa only [he] using hFilter)
    (by simpa only [rr,he,coreRho_last,coreRho,forcingRho] using hMark) (by simpa only [rr,he,coreRho_last,coreRho,forcingRho] using hProbes)
    (by simpa only [he] using hIndex) (by simpa only [he] using ht)
    (by rw [hW]; simpa only [rr,he,ef] using hf) (by rw [hW]; simpa only [rr,he,ex] using hX) (by rw [hW]; simpa only [rr,he,ey] using hY)
    (by rw [hW,ep]; exact hp)
    (by simpa only [rr,he,ef,ex,ey,ep] using (force_reindex env e up he (coreRho root) (root 34) (root 35) (root 18)
      (Source.SetLanguage.surjection 0 1 2) (args3 f X Y) p).mp hSurj)
    (by simpa only [rr,he,ey,ep] using (force_reindex env e up he (coreRho root) (root 34) (root 35) (root 18)
      (ForcingCheckOrdinal.wellorderable 0) (args1 Y) p).mp hWo)
  refine ⟨q,?_,?_,J,?_,?_⟩
  · simpa only [rr,he,coreRho_last,coreRho,forcingRho] using hq
  · simpa only [ForcingProductSymmetry.orderFormula_semantics,rr,he,ep,coreRho_last,coreRho,forcingRho] using hqp
  · simpa only [rr,he,coreRho_last,coreRho,forcingRho] using hJ
  · apply (force_reindex env e up he (coreRho root) (root 34) (root 35) (root 18)
      (Source.SetLanguage.injection 0 1 2) (args3 J Y X) q).mpr
    simpa only [rr,he,ex,ey] using hForce


/-- The SAME actual two-name parameter Q supplies all source piece equations.
Construct the slice and part graphs, then return their full surjections to the
original context. The input Cartesian NAME is retained literally. -/
private theorem graphs (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (root : Fin 40 → Fin k)
    (S f s X Y O checkedO Cart : Fin k)
    (hCore : ForcingConcreteSystem.Core hM (fun j => env (root j)))
    (hS : ForcingConjugationGraph.Subgroup (env (root 27)) (env (root 34)) (env S))
    (hSF : (Project.FirstOrderSemantics.reduct M).mem (env S) (env (root 35)))
    (hNames : ∀ j, HS actionFormula (fun a => env (coreRho root a)) (env (root 34)) (env (coreRho root 6)) (env (root 35))
      (env (ForcingMapCalculus.five f s (root 37) X Y j)))
    (hFixed : ∀ j, ForcingSupportedNames.Supported (fun a => env (coreRho root a)) (env S)
      (env (ForcingMapCalculus.five f s (root 37) X Y j)))
    {i p : M.Carrier .set} {v : Fin 2 → M.Carrier .set}
    (hi : (Project.FirstOrderSemantics.reduct M).mem i (env O))
    (hO : ForcingCheckName.Checked (env (root 1)) (env O) (env checkedO))
    (hCart : ForcingRelationGraph.Graph (orderFormula (coreRho root 0) (root 18)) ForcingCompletionGraph.trueRelation
      env (coreRho root 6) (root 1) (root 37) checkedO (env Cart))
    (hp : (Project.FirstOrderSemantics.reduct M).mem p (env (coreRho root 6)))
    (hs : MapForce env (coreRho root) (root 34) (root 35) (root 18) (env s) (env Cart) (env X) p (Source.SetLanguage.surjection 0 1 2))
    (hf : MapForce env (coreRho root) (root 34) (root 35) (root 18) (env f) (env X) (env Y) p (Source.SetLanguage.surjection 0 1 2))
    (hParam : ForcingUniformMaximum.ParameterSpec env
      (ForcingSliceParameters.parameterFormula (coreRho root) (root 34) (root 35) S (root 18) (root 1) O f s (root 37) X Y) i v) :
    ∃ Bi slice part,
      HS actionFormula (fun a => env (coreRho root a)) (env (root 34)) (env (coreRho root 6)) (env (root 35)) Bi ∧
      HS actionFormula (fun a => env (coreRho root a)) (env (root 34)) (env (coreRho root 6)) (env (root 35)) slice ∧
      HS actionFormula (fun a => env (coreRho root a)) (env (root 34)) (env (coreRho root 6)) (env (root 35)) part ∧
      MapForce env (coreRho root) (root 34) (root 35) (root 18) slice (env (root 37)) Bi p (Source.SetLanguage.surjection 0 1 2) ∧
      MapForce env (coreRho root) (root 34) (root 35) (root 18) part (v 1) (v 0) p (Source.SetLanguage.surjection 0 1 2) ∧
      ForcingPowerName.SubsetF (orderFormula (coreRho root 0) (root 18)) (domain (coreRho root) (root 34) (root 35))
        env (env (coreRho root 6)) p (v 1) Bi := by
  obtain ⟨_ho,hm0,_hj,hPres0,hG,hFilter,hw,hMu,_hI,_hD,_hMergers,_hRow,_hc,ht,_rest⟩ := hCore
  have hPres : Presentation (env (coreRho root 0)) (env (root 27)) (env (root 14)) (env (root 3)) (env (root 39))
      (env (coreRho root 1)) (env (coreRho root 2)) (env (coreRho root 3)) (env (coreRho root 4)) (env (coreRho root 5)) (env (coreRho root 6)) := by
    simpa only [coreRho,forcingRho] using hPres0
  have hm : ForcingDiagramPoset.LeftCancelMonoid (env (coreRho root 0)) (env (root 18)) (env (root 19)) := by
    simpa only [coreRho,forcingRho] using hm0
  have hNormal := ForcingNormalFilter.is_normal hM hw hMu hG hFilter
  have hpre := ForcingProductPoset.preorder env (coreRho root 0) (root 18) (coreRho root 6) hm
    hPres.2.2.2.2.1 hPres.2.2.2.1 hPres.2.2.2.2.2
  obtain ⟨ci,hCi,Bi,hBi,hFixBi,hB,hYi,hFixYi,hYP,hSi,hFixSi,hSP⟩ :=
    (ForcingSliceParameters.parameter_spec_iff env (coreRho root) (root 34) (root 35) S (root 18) (root 1) O f s (root 37) X Y i v).mp hParam
  let low : Fin (k+2) → M.Carrier .set := Fin.lastCases ci (Fin.lastCases i env)
  let b2 : Fin k → Fin (k+2) := fun j => j.castSucc.castSucc
  let rr2 : Fin 7 → Fin (k+2) := fun j => b2 (coreRho root j)
  let base : Fin (k+2) → Fin (k+6) := fun j => j.castSucc.castSucc.castSucc.castSucc
  let up : Fin k → Fin (k+6) := fun j => base (b2 j)
  let rnew : Fin 40 → Fin (k+6) := fun j => up (root j)
  let e : Fin (k+6) → M.Carrier .set := Fin.lastCases p (Fin.lastCases (v 1) (Fin.lastCases (v 0) (Fin.lastCases Bi low)))
  let ii : Fin (k+6) := base (Fin.last k).castSucc
  let cc : Fin (k+6) := base (Fin.last (k+1))
  let bi : Fin (k+6) := (Fin.last (k+2)).castSucc.castSucc.castSucc
  let yi : Fin (k+6) := (Fin.last (k+3)).castSucc.castSucc
  let si : Fin (k+6) := (Fin.last (k+4)).castSucc
  let pi : Fin (k+6) := Fin.last (k+5)
  have eb (j : Fin (k+2)) : e (base j) = low j := by simp only [e,base,Fin.lastCases_castSucc]
  have el (j : Fin k) : low (b2 j) = env j := by simp only [low,b2,Fin.lastCases_castSucc]
  have eu (j : Fin k) : e (up j) = env j := (eb (b2 j)).trans (el j)
  have ei : e ii = i := by simp only [ii,eb,low,Fin.lastCases_castSucc,Fin.lastCases_last]
  have ec : e cc = ci := by simp only [cc,eb,low,Fin.lastCases_last]
  have ebi : e bi = Bi := by simp only [e,bi,Fin.lastCases_castSucc,Fin.lastCases_last]
  have eyi : e yi = v 0 := by simp only [e,yi,Fin.lastCases_castSucc,Fin.lastCases_last]
  have esi : e si = v 1 := by simp only [e,si,Fin.lastCases_castSucc,Fin.lastCases_last]
  have ep : e pi = p := by simp only [e,pi,Fin.lastCases_last]
  have hR (a b : M.Carrier .set) : MapRel (orderFormula (rr2 0) (b2 (root 18))) low a b ↔
      MapRel (orderFormula (coreRho rnew 0) (up (root 18))) e a b := by
    simp only [ForcingProductSymmetry.orderFormula_semantics,rr2,rnew,coreRho,up,eb,el]
  have hH (a : M.Carrier .set) : ForcingClassEvaluation.Predicate (domain rr2 (b2 (root 34)) (b2 (root 35))) low a ↔
      ForcingClassEvaluation.Predicate (domain (coreRho rnew) (up (root 34)) (up (root 35))) e a := by
    simp only [domain_semantics,rr2,rnew,coreRho,up,eb,el]
  have hQB (q x : M.Carrier .set) : MapRel
      (ForcingSliceGeometry.BPredicate rr2 (b2 (root 34)) (b2 (root 35)) (b2 (root 18)) (b2 s) (b2 (root 37)) (b2 X) (Fin.last (k+1))) low q x ↔
      MapRel (ForcingSliceGeometry.BPredicate (coreRho rnew) (up (root 34)) (up (root 35)) (up (root 18)) (up s) (up (root 37)) (up X) cc) e q x := by
    simpa only [ForcingSliceGeometry.BPredicate,four_map,rr2,rnew,coreRho,up,cc] using unary_reindex low e base eb rr2
      (b2 (root 34)) (b2 (root 35)) (b2 (root 18))
      (ForcingSliceGeometry.four (b2 s) (b2 (root 37)) (b2 X) (Fin.last (k+1))) ForcingSliceGeometry.bFormula q x
  have hQY (q x : M.Carrier .set) : MapRel
      (ForcingSliceGeometry.YPredicate rr2 (b2 (root 34)) (b2 (root 35)) (b2 (root 18)) (b2 (root 1)) (b2 O) (b2 f) (b2 s) (b2 (root 37)) (b2 X) (b2 Y) (Fin.last k).castSucc) low q x ↔
      MapRel (ForcingSliceGeometry.YPredicate (coreRho rnew) (up (root 34)) (up (root 35)) (up (root 18)) (up (root 1)) (up O) (up f) (up s) (up (root 37)) (up X) (up Y) ii) e q x := by
    simp only [ForcingSliceGeometry.yPredicate_semantics]
    simpa only [rr2,rnew,coreRho,up,ii,eb] using ForcingSliceCoverage.at_reindex low e base eb rr2
      (b2 (root 34)) (b2 (root 35)) (b2 (root 18)) (b2 (root 1)) (b2 O) (b2 f) (b2 s) (b2 (root 37)) (b2 X) (b2 Y) q x (low (Fin.last k).castSucc)
  have hB' := selected_transport hR hQB hB
  have hYP' := selected_transport hR hQY hYP
  have hSP' := separated_transport hR hH hSP
  have hROld (a b : M.Carrier .set) : MapRel (orderFormula (coreRho root 0) (root 18)) env a b ↔
      MapRel (orderFormula (coreRho rnew 0) (up (root 18))) e a b := by
    simp only [ForcingProductSymmetry.orderFormula_semantics,rnew,coreRho,up,eb,el]
  have hCart' : ForcingRelationGraph.Graph (orderFormula (coreRho rnew 0) (up (root 18))) ForcingCompletionGraph.trueRelation
      e (coreRho rnew 6) (up (root 1)) (up (root 37)) (up checkedO) (e (up Cart)) := by
    rw [eu]
    apply graph_transport env e (coreRho root 6) (root 1) (root 37) checkedO
      (coreRho rnew 6) (up (root 1)) (up (root 37)) (up checkedO)
      (by simp only [rnew,coreRho,up,eb,el]) (eu (root 1)) (eu (root 37)) (eu checkedO) hROld ?_ hCart
    intro q x y
    simp only [ForcingRelationGraphForcing.Holds,ForcingCompletionGraph.trueRelation,Formula.Realize]
  have hpre' : ForcingAtomicBasic.PreorderOn (orderFormula (coreRho rnew 0) (up (root 18))) e (e (coreRho rnew 6)) := by
    simpa only [coreRho,rnew] using pre_reindex env e up eu (coreRho root) (root 18) hpre
  have hA : HS actionFormula (fun a => env (coreRho root a)) (env (root 34)) (env (coreRho root 6)) (env (root 35)) (env (root 37)) := by
    simpa only [ForcingMapCalculus.five,args3,Fin.cases_zero,Fin.cases_succ] using hNames (Fin.succ (Fin.succ 0))
  have hX : HS actionFormula (fun a => env (coreRho root a)) (env (root 34)) (env (coreRho root 6)) (env (root 35)) (env X) := by
    simpa only [ForcingMapCalculus.five,args3,args2,Fin.cases_zero,Fin.cases_succ] using hNames (Fin.succ (Fin.succ (Fin.succ 0)))
  have hY : HS actionFormula (fun a => env (coreRho root a)) (env (root 34)) (env (coreRho root 6)) (env (root 35)) (env Y) := by
    simpa only [ForcingMapCalculus.five,args3,args2,Source.SetLanguage.args1,Fin.cases_zero,Fin.cases_succ] using hNames (Fin.succ (Fin.succ (Fin.succ (Fin.succ 0))))
  have hFixf : ForcingSupportedNames.Supported (fun a => env (coreRho root a)) (env S) (env f) := by
    simpa only [ForcingMapCalculus.five,Fin.cases_zero] using hFixed 0
  have hFixs : ForcingSupportedNames.Supported (fun a => env (coreRho root a)) (env S) (env s) := by
    simpa only [ForcingMapCalculus.five,Fin.cases_zero,Fin.cases_succ] using hFixed (Fin.succ 0)
  have hFixA : ForcingSupportedNames.Supported (fun a => env (coreRho root a)) (env S) (env (root 37)) := by
    simpa only [ForcingMapCalculus.five,args3,Fin.cases_zero,Fin.cases_succ] using hFixed (Fin.succ (Fin.succ 0))
  have hFixX : ForcingSupportedNames.Supported (fun a => env (coreRho root a)) (env S) (env X) := by
    simpa only [ForcingMapCalculus.five,args3,args2,Fin.cases_zero,Fin.cases_succ] using hFixed (Fin.succ (Fin.succ (Fin.succ 0)))
  obtain ⟨slice,_hSliceGraph,hSliceHS,_hSliceFix,hSliceForce⟩ := ForcingSliceGraphs.sliceGraph_surjection hM e (coreRho rnew)
    (up (root 27)) (up (root 14)) (up (root 3)) (up (root 39)) (up (root 34)) (up (root 35)) (up S)
    (up (root 18)) (up (root 1)) (up s) (up (root 37)) (up X) (up O) (up checkedO) ii cc bi (up Cart) pi
    (by simpa only [rnew,coreRho,up,eb,el] using hPres) (by simpa only [eu] using hG) (by simpa only [eu] using hNormal)
    (by simpa only [eu] using hS) (by simpa only [eu] using hSF) (by simpa only [eu] using ht) hpre'
    (by simpa only [rnew,coreRho,up,eb,el] using hA) (by simpa only [rnew,coreRho,up,eb,el] using hX)
    (by simpa only [rnew,coreRho,up,eb,el,ebi] using hBi)
    (by simpa only [rnew,coreRho,up,eb,el] using hFixs) (by simpa only [rnew,coreRho,up,eb,el] using hFixA)
    (by simpa only [rnew,coreRho,up,eb,el] using hFixX) (by simpa only [rnew,coreRho,up,eb,el,ebi] using hFixBi)
    (by simpa only [eu] using hO) (by simpa only [ei,eu] using hi) (by simpa only [ec,ei,eu] using hCi)
    (by simpa only [rnew,coreRho,up,eb,el,ebi] using hB') hCart'
    (by simpa only [rnew,coreRho,up,eb,el,ep] using hp)
    (by simpa only [rnew,coreRho,up,eb,el,ep] using
      (force_reindex env e up eu (coreRho root) (root 34) (root 35) (root 18) (Source.SetLanguage.mapsTo 0 1 2)
        (args3 (env s) (env Cart) (env X)) p).mp (ForcingImageQuotient.surjection_mapsTo_reuse hM hpre hp hs))
  obtain ⟨part,_hPartGraph,hPartHS,_hPartFix,hPartForce⟩ := ForcingSliceGraphs.partGraph_surjection hM e (coreRho rnew)
    (up (root 27)) (up (root 14)) (up (root 3)) (up (root 39)) (up (root 34)) (up (root 35)) (up S)
    (up (root 18)) (up (root 1)) (up O) (up f) (up s) (up (root 37)) (up X) (up Y) ii cc bi yi si pi
    (by simpa only [rnew,coreRho,up,eb,el] using hPres) (by simpa only [eu] using hG) (by simpa only [eu] using hNormal)
    (by simpa only [eu] using hS) (by simpa only [eu] using hSF) (by simpa only [eu] using ht) hpre'
    (by simpa only [rnew,coreRho,up,eb,el] using hX) (by simpa only [rnew,coreRho,up,eb,el] using hY)
    (by simpa only [rnew,coreRho,up,eb,el,eyi] using hYi) (by simpa only [rnew,coreRho,up,eb,el,esi] using hSi)
    (by simpa only [rnew,coreRho,up,eb,el] using hFixf)
    (by simpa only [rnew,coreRho,up,eb,el,eyi] using hFixYi) (by simpa only [rnew,coreRho,up,eb,el,esi] using hFixSi)
    (by simpa only [ec,ei,eu] using hCi) (by simpa only [rnew,coreRho,up,eb,el,ebi] using hB')
    (by simpa only [rnew,coreRho,up,eb,el,eyi] using hYP')
    (by simpa only [rnew,coreRho,up,eb,el,ebi,eyi,esi] using hSP')
    (by simpa only [rnew,coreRho,up,eb,el,ep] using hp)
    (by simpa only [rnew,coreRho,up,eb,el,ep] using
      (force_reindex env e up eu (coreRho root) (root 34) (root 35) (root 18) (Source.SetLanguage.mapsTo 0 1 2)
        (args3 (env f) (env X) (env Y)) p).mp (ForcingImageQuotient.surjection_mapsTo_reuse hM hpre hp hf))
  refine ⟨Bi,slice,part,hBi,?_,?_,?_,?_,?_⟩
  · simpa only [rnew,coreRho,up,eb,el] using hSliceHS
  · simpa only [rnew,coreRho,up,eb,el] using hPartHS
  · apply (force_reindex env e up eu (coreRho root) (root 34) (root 35) (root 18)
      (Source.SetLanguage.surjection 0 1 2) (args3 slice (env (root 37)) Bi) p).mpr
    simpa only [rnew,coreRho,up,eb,el,ebi,ep] using hSliceForce
  · apply (force_reindex env e up eu (coreRho root) (root 34) (root 35) (root 18)
      (Source.SetLanguage.surjection 0 1 2) (args3 part (v 1) (v 0)) p).mpr
    simpa only [rnew,coreRho,up,eb,el,eyi,esi,ep] using hPartForce
  · have hRLow (a b : M.Carrier .set) : MapRel (orderFormula (coreRho root 0) (root 18)) env a b ↔
        MapRel (orderFormula (rr2 0) (b2 (root 18))) low a b := by
      simp only [ForcingProductSymmetry.orderFormula_semantics,rr2,el]
    have hpreLow : ForcingAtomicBasic.PreorderOn (orderFormula (rr2 0) (b2 (root 18))) low (env (coreRho root 6)) := by
      simpa only [rr2,el] using pre_reindex env low b2 el (coreRho root) (root 18) hpre
    intro nu _hNu q hq _hqp hMem
    have hLow := (ForcingSeparation.atomic_congr hRLow false (env (coreRho root 6)) nu (v 1) q).mp hMem
    have hLowBi := ((ForcingSliceGeometry.mem_Spart hM hpreLow hSP hq).mp hLow).1
    exact (ForcingSeparation.atomic_congr hRLow false (env (coreRho root 6)) nu Bi q).mpr hLowBi

/-- Pinned source SliceAssembly.slice_candidate:118–156. Both cases consume
the actual parameter names; no candidate, default family or classification
oracle is assumed. The only background Choice/order will be discharged in L. -/
theorem slice_candidate (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (hOrder : Project.Gw_order_d (InnerModel.Js_lt_d (M := Project.FirstOrderSemantics.reduct M)))
    (hChoice : ConstructionDirectedCardinality.Choice (M := M))
    (env : Fin k → M.Carrier .set) (root : Fin 40 → Fin k)
    (S f s X Y O checkedO Cart : Fin k)
    (hCore : ForcingConcreteSystem.Core hM (fun j => env (root j)))
    (hS : ForcingConjugationGraph.Subgroup (env (root 27)) (env (root 34)) (env S))
    (hSF : (Project.FirstOrderSemantics.reduct M).mem (env S) (env (root 35)))
    (hNames : ∀ j, HS actionFormula (fun a => env (coreRho root a)) (env (root 34)) (env (coreRho root 6)) (env (root 35))
      (env (ForcingMapCalculus.five f s (root 37) X Y j)))
    (hFixed : ∀ j, ForcingSupportedNames.Supported (fun a => env (coreRho root a)) (env S)
      (env (ForcingMapCalculus.five f s (root 37) X Y j)))
    {i p : M.Carrier .set} {v : Fin 2 → M.Carrier .set}
    (hi : (Project.FirstOrderSemantics.reduct M).mem i (env O))
    (hO : ForcingCheckName.Checked (env (root 1)) (env O) (env checkedO))
    (hCart : ForcingRelationGraph.Graph (orderFormula (coreRho root 0) (root 18)) ForcingCompletionGraph.trueRelation
      env (coreRho root 6) (root 1) (root 37) checkedO (env Cart))
    (hp : (Project.FirstOrderSemantics.reduct M).mem p (env (coreRho root 6)))
    (hs : MapForce env (coreRho root) (root 34) (root 35) (root 18) (env s) (env Cart) (env X) p (Source.SetLanguage.surjection 0 1 2))
    (hf : MapForce env (coreRho root) (root 34) (root 35) (root 18) (env f) (env X) (env Y) p (Source.SetLanguage.surjection 0 1 2))
    (hParam : ForcingUniformMaximum.ParameterSpec env
      (ForcingSliceParameters.parameterFormula (coreRho root) (root 34) (root 35) S (root 18) (root 1) O f s (root 37) X Y) i v) :
    ForcingWellorderedTarget.Result env (coreRho root) (root 34) (root 35) (root 18) (v 1) (v 0) p := by
  classical
  have hCoreSaved := hCore
  have hOutcome := ForcingConcreteSystem.consequences hM hOrder hChoice (fun j => env (root j)) hCore
  obtain ⟨_ho,hm0,_hj,hPres0,hG,hFilter,hw,hMu,_hI,_hD,_hMergers,_hRow,_hc,ht,_rest⟩ := hCoreSaved
  have hPres : Presentation (env (coreRho root 0)) (env (root 27)) (env (root 14)) (env (root 3)) (env (root 39))
      (env (coreRho root 1)) (env (coreRho root 2)) (env (coreRho root 3)) (env (coreRho root 4)) (env (coreRho root 5)) (env (coreRho root 6)) := by
    simpa only [coreRho,forcingRho] using hPres0
  have hm : ForcingDiagramPoset.LeftCancelMonoid (env (coreRho root 0)) (env (root 18)) (env (root 19)) := by
    simpa only [coreRho,forcingRho] using hm0
  have hNormal := ForcingNormalFilter.is_normal hM hw hMu hG hFilter
  have hpre := ForcingProductPoset.preorder env (coreRho root 0) (root 18) (coreRho root 6) hm
    hPres.2.2.2.2.1 hPres.2.2.2.1 hPres.2.2.2.2.2
  have hA : HS actionFormula (fun a => env (coreRho root a)) (env (root 34)) (env (coreRho root 6)) (env (root 35)) (env (root 37)) := by
    simpa only [ForcingMapCalculus.five,args3,Fin.cases_zero,Fin.cases_succ] using hNames (Fin.succ (Fin.succ 0))
  have hYP := ForcingSliceParameters.parameter_hs env (coreRho root) (root 34) (root 35) S (root 18) (root 1) O f s (root 37) X Y hParam
  have hYi := hYP (0 : Fin 2)
  have hSi := hYP (1 : Fin 2)
  obtain ⟨Bi,slice,part,hBi,hSlice,hPart,hSliceSurj,hPartSurj,hSubset⟩ :=
    graphs hM env root S f s X Y O checkedO Cart hCore hS hSF hNames hFixed hi hO hCart hp hs hf hParam
  let R := orderFormula (coreRho root 0) (root 18)
  let H := domain (coreRho root) (root 34) (root 35)
  let W := env (coreRho root 6)
  have mono {n : Nat} {phi : Formula n} {names : Fin n → M.Carrier .set} {a b : M.Carrier .set}
      (ha : (Project.FirstOrderSemantics.reduct M).mem a W)
      (hb : (Project.FirstOrderSemantics.reduct M).mem b W)
      (hba : MapRel R env b a) (hF : Force R H env names W a phi) : Force R H env names W b phi :=
    ForcingFormula.mono hM hpre phi names ha hb hba hF
  by_cases hwo : ∃ q, (Project.FirstOrderSemantics.reduct M).mem q W ∧ MapRel R env q p ∧
      Force R H env (args1 (v 0)) W q (ForcingCheckOrdinal.wellorderable 0)
  · obtain ⟨q,hq,hqp,hwo⟩ := hwo
    obtain ⟨r,hr,hrq,J,hJ,hForce⟩ := wellordered_target hM hChoice env root hCore hPart hSi hYi hq
      (mono hp hq hqp hPartSurj) hwo
    exact ⟨r,hr,hpre.2 r q p hr hq hp hrq hqp,J,hJ,hForce⟩
  · have hYn : Force R H env (args1 (v 0)) W p (ForcingCheckOrdinal.wellorderable 0).neg := by
      apply (ForcingFormula.force_neg hM hpre hp _ _).mpr
      intro q hq hqp hWo
      exact hwo ⟨q,hq,hqp,hWo⟩
    have hSn : Force R H env (args1 (v 1)) W p (ForcingCheckOrdinal.wellorderable 0).neg := by
      apply (ForcingFormula.force_neg hM hpre hp _ _).mpr
      intro q hq hqp hWo
      exact hwo ⟨q,hq,hqp,image_wellorderable env (coreRho root) (root 27) (root 14) (root 3) (root 39)
        (root 34) (root 35) (root 18) (root 1) hM hPres hG hNormal ht hpre hPart hSi hYi hq
        (mono hp hq hqp hPartSurj) hWo⟩
    obtain ⟨q,hq,hqp,d,hd,hMem⟩ := member_raw env (coreRho root) (root 27) (root 14) (root 3) (root 39)
      (root 34) (root 35) (root 18) (root 1) hM hPres hG hNormal ht hpre hSi hp hSn
    have hSubQ : ForcingPowerName.SubsetF R H env W q (v 1) Bi := by
      intro x hx r hr hrq hxS
      exact hSubset x hx r hr (hpre.2 r q p hr hq hp hrq hqp) hxS
    obtain ⟨aS,haS,hASurj⟩ := subset_surjection env (coreRho root) (root 27) (root 14) (root 3) (root 39)
      (root 34) (root 35) (root 18) (root 1) hM hPres hG hNormal ht hpre hSlice hA hSi hd hq
      (mono hp hq hqp hSliceSurj) hSubQ hMem
    obtain ⟨aY,haY,hAYLaws⟩ := compose env (coreRho root) (root 27) (root 14) (root 3) (root 39)
      (root 34) (root 35) (root 18) (root 1) hM hPres hG hNormal ht hpre haS hPart hA hSi hYi
    have hAYSurj := (hAYLaws q hq).2.1 hASurj (mono hp hq hqp hPartSurj)
    obtain ⟨r,hr,hrq,kS,hkS,hKS⟩ := image_bijection hM env root hCore hOutcome haS hSi hq hASurj
      (mono hp hq hqp hSn)
    have hrp := hpre.2 r q p hr hq hp hrq hqp
    obtain ⟨t,htW,htr,kY,hkY,hKY⟩ := image_bijection hM env root hCore hOutcome haY hYi hr
      (mono hq hr hrq hAYSurj) (mono hp hr hrp hYn)
    have hKS' := (ForcingFormula.force_conj R H env (args3 kS (env (root 37)) (v 1)) W t _ _).mp
      (mono hr htW htr hKS)
    have hKY' := (ForcingFormula.force_conj R H env (args3 kY (env (root 37)) (v 0)) W t _ _).mp hKY
    obtain ⟨inv,hInv,hInvLaws⟩ := inverse env (coreRho root) (root 27) (root 14) (root 3) (root 39)
      (root 34) (root 35) (root 18) (root 1) hM hPres hG hNormal ht hpre hkY hA hYi
    have hInvInj := (hInvLaws t htW hKY'.1 hKY'.2).2
    obtain ⟨J,hJ,hJLaws⟩ := compose env (coreRho root) (root 27) (root 14) (root 3) (root 39)
      (root 34) (root 35) (root 18) (root 1) hM hPres hG hNormal ht hpre hInv hkS hYi hA hSi
    exact ⟨t,htW,hpre.2 t r p htW hr hp htr hrp,J,hJ,(hJLaws t htW).2.2 hInvInj hKS'.2⟩


/-- The actual source existential injection, below every internal condition. -/
theorem parameter_forces_exists (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (hOrder : Project.Gw_order_d (InnerModel.Js_lt_d (M := Project.FirstOrderSemantics.reduct M)))
    (hChoice : ConstructionDirectedCardinality.Choice (M := M))
    (env : Fin k → M.Carrier .set) (root : Fin 40 → Fin k)
    (S f s X Y O checkedO Cart : Fin k)
    (hCore : ForcingConcreteSystem.Core hM (fun j => env (root j)))
    (hS : ForcingConjugationGraph.Subgroup (env (root 27)) (env (root 34)) (env S))
    (hSF : (Project.FirstOrderSemantics.reduct M).mem (env S) (env (root 35)))
    (hNames : ∀ j, HS actionFormula (fun a => env (coreRho root a)) (env (root 34)) (env (coreRho root 6)) (env (root 35))
      (env (ForcingMapCalculus.five f s (root 37) X Y j)))
    (hFixed : ∀ j, ForcingSupportedNames.Supported (fun a => env (coreRho root a)) (env S)
      (env (ForcingMapCalculus.five f s (root 37) X Y j)))
    {i p : M.Carrier .set} {v : Fin 2 → M.Carrier .set}
    (hi : (Project.FirstOrderSemantics.reduct M).mem i (env O))
    (hO : ForcingCheckName.Checked (env (root 1)) (env O) (env checkedO))
    (hCart : ForcingRelationGraph.Graph (orderFormula (coreRho root 0) (root 18)) ForcingCompletionGraph.trueRelation
      env (coreRho root 6) (root 1) (root 37) checkedO (env Cart))
    (hp : (Project.FirstOrderSemantics.reduct M).mem p (env (coreRho root 6)))
    (hs : MapForce env (coreRho root) (root 34) (root 35) (root 18) (env s) (env Cart) (env X) p (Source.SetLanguage.surjection 0 1 2))
    (hf : MapForce env (coreRho root) (root 34) (root 35) (root 18) (env f) (env X) (env Y) p (Source.SetLanguage.surjection 0 1 2))
    (hParam : ForcingUniformMaximum.ParameterSpec env
      (ForcingSliceParameters.parameterFormula (coreRho root) (root 34) (root 35) S (root 18) (root 1) O f s (root 37) X Y) i v) :
    Force (orderFormula (coreRho root 0) (root 18)) (domain (coreRho root) (root 34) (root 35)) env v
      (env (coreRho root 6)) p (.ex (Source.SetLanguage.injection 2 0 1)) := by
  have hCoreSaved := hCore
  obtain ⟨_ho,hm0,_hj,hPres0,hG,hFilter,hw,hMu,_hI,_hD,_hMergers,_hRow,_hc,ht,_rest⟩ := hCoreSaved
  have hPres : Presentation (env (coreRho root 0)) (env (root 27)) (env (root 14)) (env (root 3)) (env (root 39))
      (env (coreRho root 1)) (env (coreRho root 2)) (env (coreRho root 3)) (env (coreRho root 4)) (env (coreRho root 5)) (env (coreRho root 6)) := by
    simpa only [coreRho,forcingRho] using hPres0
  have hm : ForcingDiagramPoset.LeftCancelMonoid (env (coreRho root 0)) (env (root 18)) (env (root 19)) := by
    simpa only [coreRho,forcingRho] using hm0
  have hpre := ForcingProductPoset.preorder env (coreRho root 0) (root 18) (coreRho root 6) hm
    hPres.2.2.2.2.1 hPres.2.2.2.1 hPres.2.2.2.2.2
  apply (ForcingFormula.force_ex _ _ _ _ _ _ _).mpr
  intro q hq hqp
  obtain ⟨r,hr,hrq,J,hJ,hForce⟩ := slice_candidate hM hOrder hChoice env root S f s X Y O checkedO Cart
    hCore hS hSF hNames hFixed hi hO hCart hq
    (ForcingFormula.mono hM hpre _ _ hp hq hqp hs) (ForcingFormula.mono hM hpre _ _ hp hq hqp hf) hParam
  refine ⟨r,hr,hrq,J,(domain_semantics _ _ _ _ _).mpr hJ,?_⟩
  rw [Source.SetLanguage.injection,ForcingSound.rename hM hpre _ _ _ _ hr] at hForce ⊢
  have hv : (fun j => Fin.lastCases J v (args3 (2 : Fin 3) 0 1 j)) =
      (fun j => args3 J (v 0) (v 1) (args3 (0 : Fin 3) 1 2 j)) := by
    funext j
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun t => Fin.elim0 t))) j
  rw [hv]
  exact hForce

/-- All FOUR actual source inputs: totality, literal uniqueness, fixedness and
forced injection existence. No parameter graph or candidate family is assumed. -/
theorem uniform_inputs (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (hOrder : Project.Gw_order_d (InnerModel.Js_lt_d (M := Project.FirstOrderSemantics.reduct M)))
    (hChoice : ConstructionDirectedCardinality.Choice (M := M))
    (env : Fin k → M.Carrier .set) (root : Fin 40 → Fin k)
    (S f s X Y O checkedO Cart : Fin k)
    (hCore : ForcingConcreteSystem.Core hM (fun j => env (root j)))
    (hS : ForcingConjugationGraph.Subgroup (env (root 27)) (env (root 34)) (env S))
    (hSF : (Project.FirstOrderSemantics.reduct M).mem (env S) (env (root 35)))
    (hNames : ∀ j, HS actionFormula (fun a => env (coreRho root a)) (env (root 34)) (env (coreRho root 6)) (env (root 35))
      (env (ForcingMapCalculus.five f s (root 37) X Y j)))
    (hFixed : ∀ j, ForcingSupportedNames.Supported (fun a => env (coreRho root a)) (env S)
      (env (ForcingMapCalculus.five f s (root 37) X Y j)))
    {p : M.Carrier .set}
    (hO : ForcingCheckName.Checked (env (root 1)) (env O) (env checkedO))
    (hCart : ForcingRelationGraph.Graph (orderFormula (coreRho root 0) (root 18)) ForcingCompletionGraph.trueRelation
      env (coreRho root 6) (root 1) (root 37) checkedO (env Cart))
    (hp : (Project.FirstOrderSemantics.reduct M).mem p (env (coreRho root 6)))
    (hs : MapForce env (coreRho root) (root 34) (root 35) (root 18) (env s) (env Cart) (env X) p (Source.SetLanguage.surjection 0 1 2))
    (hf : MapForce env (coreRho root) (root 34) (root 35) (root 18) (env f) (env X) (env Y) p (Source.SetLanguage.surjection 0 1 2)) :
    ForcingUniformMaximum.Inputs env (coreRho root) (root 34) (root 35) (root 18) (env S) p (env O)
      (ForcingSliceParameters.parameterFormula (coreRho root) (root 34) (root 35) S (root 18) (root 1) O f s (root 37) X Y)
      (Source.SetLanguage.injection 2 0 1) := by
  have hCoreSaved := hCore
  obtain ⟨_ho,_hm,_hj,hPres0,hG,hFilter,hw,hMu,_hI,_hD,_hMergers,_hRow,_hc,ht,_rest⟩ := hCoreSaved
  have hNormal := ForcingNormalFilter.is_normal hM hw hMu hG hFilter
  have hPres : Presentation (env (coreRho root 0)) (env (root 27)) (env (root 14)) (env (root 3)) (env (root 39))
      (env (coreRho root 1)) (env (coreRho root 2)) (env (coreRho root 3)) (env (coreRho root 4)) (env (coreRho root 5)) (env (coreRho root 6)) := by
    simpa only [coreRho,forcingRho] using hPres0
  refine ⟨?_,?_,?_,?_⟩
  · intro i _hi
    exact ForcingSliceParameters.parameter_exists hM env (coreRho root) (root 27) (root 14) (root 3) (root 39)
      (root 34) (root 35) S (root 18) (root 1) O f s (root 37) X Y hPres hG hNormal hS hSF ht hNames hFixed i
  · intro i _hi v v' hv hv'
    exact ForcingSliceParameters.parameter_unique hM env (coreRho root) (root 34) (root 35) S (root 18) (root 1) O f s (root 37) X Y hv hv'
  · intro i _hi v hv
    exact ForcingSliceParameters.parameter_fixed env (coreRho root) (root 34) (root 35) S (root 18) (root 1) O f s (root 37) X Y hv
  · intro i hi v hv
    exact parameter_forces_exists hM hOrder hChoice env root S f s X Y O checkedO Cart hCore hS hSF hNames hFixed hi hO hCart hp hs hf hv

/-- The existing uniform maximum constructs the actual set-coded candidate
FUNCTION and its one common support, on ALL internal slice indices. -/
theorem candidate_family (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (hOrder : Project.Gw_order_d (InnerModel.Js_lt_d (M := Project.FirstOrderSemantics.reduct M)))
    (hChoice : ConstructionDirectedCardinality.Choice (M := M))
    (env : Fin k → M.Carrier .set) (root : Fin 40 → Fin k)
    (S f s X Y O checkedO Cart : Fin k)
    (hCore : ForcingConcreteSystem.Core hM (fun j => env (root j)))
    (hS : ForcingConjugationGraph.Subgroup (env (root 27)) (env (root 34)) (env S))
    (hSF : (Project.FirstOrderSemantics.reduct M).mem (env S) (env (root 35)))
    (hNames : ∀ j, HS actionFormula (fun a => env (coreRho root a)) (env (root 34)) (env (coreRho root 6)) (env (root 35))
      (env (ForcingMapCalculus.five f s (root 37) X Y j)))
    (hFixed : ∀ j, ForcingSupportedNames.Supported (fun a => env (coreRho root a)) (env S)
      (env (ForcingMapCalculus.five f s (root 37) X Y j)))
    {p : M.Carrier .set}
    (hO : ForcingCheckName.Checked (env (root 1)) (env O) (env checkedO))
    (hCart : ForcingRelationGraph.Graph (orderFormula (coreRho root 0) (root 18)) ForcingCompletionGraph.trueRelation
      env (coreRho root 6) (root 1) (root 37) checkedO (env Cart))
    (hp : (Project.FirstOrderSemantics.reduct M).mem p (env (coreRho root 6)))
    (hs : MapForce env (coreRho root) (root 34) (root 35) (root 18) (env s) (env Cart) (env X) p (Source.SetLanguage.surjection 0 1 2))
    (hf : MapForce env (coreRho root) (root 34) (root 35) (root 18) (env f) (env X) (env Y) p (Source.SetLanguage.surjection 0 1 2)) :
    ForcingUniformMaximum.Result env (coreRho root) (root 27) (root 34) (root 35) (root 18) p (env O)
      (ForcingSliceParameters.parameterFormula (coreRho root) (root 34) (root 35) S (root 18) (root 1) O f s (root 37) X Y)
      (Source.SetLanguage.injection 2 0 1) := by
  have hInputs := uniform_inputs hM hOrder hChoice env root S f s X Y O checkedO Cart hCore hS hSF hNames hFixed hO hCart hp hs hf
  obtain ⟨hProbes,hIndex⟩ := ForcingRootProbes.on_core hM (fun j => env (root j)) hCore
  obtain ⟨_ho,hm,_hj,hPres,hG,hFilter,hw,hMu,hI,hD,hMergers,hRow,_hc,_ht,_hl,_hb,_hObj,hMark,hCard,_rest⟩ := hCore
  apply ForcingUniformMaximum.uniform_maximum_dense hM hChoice env (coreRho root)
    (root 39) (root 13) (root 16) (root 14) (root 19) (root 20) (root 21) (root 22) (root 23) (root 24)
    (root 27) (root 14) (root 3) (root 34) (root 35) (root 18) (root 13)
    _ _ (env S) p (env O) hw hMu hI
    (by simpa only [coreRho,forcingRho] using hD) hCard hMergers
    (by simpa only [coreRho,forcingRho] using hRow)
    (by simpa only [coreRho,forcingRho] using hm)
    (by simpa only [coreRho,forcingRho] using hPres) hG hFilter
    (by simpa only [coreRho,forcingRho] using hMark)
    (by simpa only [coreRho,forcingRho] using hProbes) hIndex hSF hp hInputs


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

/-- Actual SliceAssembly input and actual internal candidate function output.
The formal relation Q is the completed two-name parameter constructor. -/
def sentence {k : Nat} (root : Fin 40 → Fin k) (S f s X Y O checkedO Cart p : Fin k) : Project.Sentence where
  formula :=
    let rho := coreRho root
    let Q := ForcingSliceParameters.parameterFormula rho (root 34) (root 35) S (root 18) (root 1) O f s (root 37) X Y
    Project.Formula.forallClosure k
      ([ForcingConcreteSystem.coreFormula.rename root,
        ProjectSyntax.encode id (ForcingConjugationGraph.subgroup (root 27) (root 34) S),
        .mem (.bound S) (.bound (root 35)),
        ProjectSyntax.encode id (ForcingHS.hs actionFormula rho (root 34) (rho 6) (root 35) f),
        ProjectSyntax.encode id (ForcingHS.hs actionFormula rho (root 34) (rho 6) (root 35) s),
        ProjectSyntax.encode id (ForcingHS.hs actionFormula rho (root 34) (rho 6) (root 35) (root 37)),
        ProjectSyntax.encode id (ForcingHS.hs actionFormula rho (root 34) (rho 6) (root 35) X),
        ProjectSyntax.encode id (ForcingHS.hs actionFormula rho (root 34) (rho 6) (root 35) Y),
        ProjectSyntax.encode id (ForcingSupportingRoot.tupleSupported rho S (ForcingMapCalculus.five f s (root 37) X Y)),
        ProjectSyntax.encode id (ForcingCheckName.checkName (root 1) O checkedO),
        ProjectSyntax.encode id (ForcingRelationGraph.graph (orderFormula (rho 0) (root 18)) ForcingCompletionGraph.trueRelation id
          (rho 6) (root 1) (root 37) checkedO Cart),
        .mem (.bound p) (.bound (rho 6)),
        ProjectSyntax.encode id (ForcingFormula.formula (orderFormula (rho 0) (root 18)) (domain rho (root 34) (root 35)) id
          (args3 s Cart X) (rho 6) p (Source.SetLanguage.surjection 0 1 2)),
        ProjectSyntax.encode id (ForcingFormula.formula (orderFormula (rho 0) (root 18)) (domain rho (root 34) (root 35)) id
          (args3 f X Y) (rho 6) p (Source.SetLanguage.surjection 0 1 2))].foldr Definitional.Formula.imp
        (.conj (ProjectSyntax.encode id (ForcingUniformMaximum.inputs rho (root 34) (root 35) (root 18) S p O Q (Source.SetLanguage.injection 2 0 1)))
          (ProjectSyntax.encode id (ForcingUniformMaximum.resultFormula rho (root 27) (root 34) (root 35) (root 18) p O Q (Source.SetLanguage.injection 2 0 1)))))
  freeClosed := by
    simp -implicitDefEqProofs [List.foldr,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
      Definitional.Formula.freeClosed_rename,ForcingConcreteSystem.coreFormula_freeClosed]

theorem models {k : Nat} (root : Fin 40 → Fin k) (S f s X Y O checkedO Cart p : Fin k)
    (hM : FirstOrder.Theory.Models M nativeZF)
    (hOrder : Project.Gw_order_d (InnerModel.Js_lt_d (M := Project.FirstOrderSemantics.reduct M)))
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) :
    (Project.fo_sentence (sentence root S f s X Y O checkedO Cart p)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM),SetTheory.Structure.satisfiesSentence_iff]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro env
  simp only [List.foldr,Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,core_renamed_semantics hM,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ForcingConjugationGraph.subgroup_semantics,
    ForcingHS.hs_semantics,ForcingSupportingRoot.tupleSupported_semantics,ForcingCheckName.checkName_semantics,
    ForcingRelationGraph.graph_semantics,ForcingFormula.formula_semantics,ForcingUniformMaximum.inputs_semantics,
    ForcingUniformMaximum.resultFormula_semantics,id_eq,args3_map]
  intro hCore hS hSF hfHS hsHS hAHS hXHS hYHS hFixed hO hCart hp hs hf
  have hNames : ∀ j, HS actionFormula (fun a => env (coreRho root a)) (env (root 34)) (env (coreRho root 6)) (env (root 35))
      (env (ForcingMapCalculus.five f s (root 37) X Y j)) := by
    intro j
    exact Fin.cases hfHS (Fin.cases hsHS (Fin.cases hAHS (Fin.cases hXHS (Fin.cases hYHS (fun t => Fin.elim0 t))))) j
  exact ⟨uniform_inputs hM hOrder hChoice env root S f s X Y O checkedO Cart hCore hS hSF hNames hFixed hO hCart hp hs hf,
    candidate_family hM hOrder hChoice env root S f s X Y O checkedO Cart hCore hS hSF hNames hFixed hO hCart hp hs hf⟩

/-- Ordinary nativeZF original-kernel derivation. The SAME completed L
interpretation discharges both background Choice and the L-order; neither
is an added external assumption of this object theorem. -/
theorem kernel_certificate {k : Nat} (root : Fin 40 → Fin k) (S f s X Y O checkedO Cart p : Fin k) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (ConstructibleGround.relative
      (sentence root S f s X Y O checkedO Cart p))) := by
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
    (models root S f s X Y O checkedO Cart p hL (ConstructionRoundSelection.l_order hN) hChoice)

end PPAC.Migration.ForcingSliceCandidate
