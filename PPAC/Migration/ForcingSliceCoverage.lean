/- Pinned SliceGeometry.Spart_disjoint/occurrence_cover/Ypart_cover.
Actual source surjections and the existing Cartesian/check-name equations
supply dense INTERNAL slice indices. No choice of slice indices/defaults,
external wellorder, or assertion that Spart covers X. -/
import PPAC.Migration.ForcingSliceGraphs

namespace PPAC.Migration.ForcingSliceCoverage
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
open ForcingRelationGraphForcing (Holds)
open ForcingSliceGeometry (four occurrence occurrenceFormula)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 400000
universe u v
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

private theorem five_map {a : Type v} {b : Type u} (g : a → b) (f s A X Y : a) :
    (fun j => g (ForcingMapCalculus.five f s A X Y j)) =
      ForcingMapCalculus.five (g f) (g s) (g A) (g X) (g Y) := by
  funext j
  exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun t => Fin.elim0 t))))) j

private theorem app_congr (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    {R : Formula (k+2)} {H : Formula (k+1)} {env : Fin k → M.Carrier .set}
    {P p f g x x' y y' : M.Carrier .set} (hpre : ForcingAtomicBasic.PreorderOn R env P)
    (hp : (Project.FirstOrderSemantics.reduct M).mem p P)
    (hf : Forces true R env P f g p) (hx : Forces true R env P x x' p) (hy : Forces true R env P y y' p)
    (hh : Force R H env (args3 f x y) P p (Source.SetLanguage.edge 0 1 2)) :
    Force R H env (args3 g x' y') P p (Source.SetLanguage.edge 0 1 2) := by
  apply (ForcingFormula.tuple_congr hM hpre (Source.SetLanguage.edge 0 1 2) _ _ p hp ?_).mp hh
  intro j
  exact Fin.cases hf (Fin.cases hx (Fin.cases hy (fun i => Fin.elim0 i))) j

/-- The source regular occurrence cover, directly from BOTH full source
surjections. Every pair/check witness is actually constructed at a refinement. -/
theorem occurrence_cover (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k)
    (I K B w G F mul top s f A X Y O checkedO Cart p : Fin k)
    (hPres : Presentation (env (rho 0)) (env I) (env K) (env B) (env w)
      (env (rho 1)) (env (rho 2)) (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hG : ForcingLabelPermutations.Carrier (env I) (env G))
    (hF : ForcingNormalFilter.Normal (env I) (env G) (env F))
    (ht : ForcingWithTopCarrier.Empty (env top))
    (hpre : ForcingAtomicBasic.PreorderOn (orderFormula (rho 0) mul) env (env (rho 6)))
    (hA : HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) (env A))
    (hO : ForcingCheckName.Checked (env top) (env O) (env checkedO))
    (hCart : ForcingRelationGraph.Graph (orderFormula (rho 0) mul) ForcingCompletionGraph.trueRelation
      env (rho 6) top A checkedO (env Cart))
    (hp : (Project.FirstOrderSemantics.reduct M).mem (env p) (env (rho 6)))
    (hs : Force (orderFormula (rho 0) mul) (domain rho G F) env (args3 (env s) (env Cart) (env X))
      (env (rho 6)) (env p) (Source.SetLanguage.surjection 0 1 2))
    (hf : Force (orderFormula (rho 0) mul) (domain rho G F) env (args3 (env f) (env X) (env Y))
      (env (rho 6)) (env p) (Source.SetLanguage.surjection 0 1 2)) :
    ForcingLeastRelation.Cover (orderFormula (rho 0) mul) (occurrence rho G F mul top f s A X Y)
      (domain rho G F) env (env (rho 6)) (env O) (env Y) (env p) := by
  let R := orderFormula (rho 0) mul
  let H := domain rho G F
  let W := env (rho 6)
  let v7 : Fin 7 → M.Carrier .set := fun j => env (rho j)
  have htW := (hPres.2.2.2.2.2 (env top)).mpr (Or.inl ht)
  have hTop : ∀ a, (Project.FirstOrderSemantics.reduct M).mem a W → MapRel R env a (env top) :=
    fun a _ => (orderFormula_semantics env (rho 0) mul a (env top)).mpr (Or.inl ht)
  have hCOHS := ForcingSectionInjection.checked_hs hM v7 hPres hG hF ht hO
  intro y hy q hq hqp hyY r hr hrq
  obtain ⟨a1,ha1,ha1r,x,hx,hxX,hAppF⟩ := ForcingImageQuotient.surjection_onto_reuse hM hpre hp hf hy hq hqp hyY hr hrq
  have ha1q := hpre.2 a1 r q ha1 hr hq ha1r hrq
  have ha1p := hpre.2 a1 q (env p) ha1 hq hp ha1q hqp
  obtain ⟨a2,ha2,ha2a1,z,_hz,hzCart,hAppS⟩ := ForcingImageQuotient.surjection_onto_reuse hM hpre hp hs
    hx ha1 ha1p hxX ha1 (hpre.1 a1 ha1)
  obtain ⟨a3,ha3,ha3a2,a,j,pair,ha,hj,hPair,haA,hjO,_hTrue,hzPair⟩ :=
    ((ForcingCompletionGraph.cartesian_mem hM env rho G F mul top A checkedO hPres ht hpre hA hCOHS hCart ha2).mp hzCart)
      a2 ha2 (hpre.1 a2 ha2)
  obtain ⟨a4,ha4,ha4a3,i,hi,ci,hCi,hjCi⟩ := (ForcingInfinity.mem_check hM hO htW hTop ha3).mp hjO
    a3 ha3 (hpre.1 a3 ha3)
  have haHS := (ForcingRelationGraphApplication.hs_actionAt env rho _ _ _ _).mp ha
  have hCiHS := ForcingSectionInjection.checked_hs hM v7 hPres hG hF ht hCi
  obtain ⟨pair',hPair'⟩ := ForcingOrderedPairName.exists_orderedPairName hM (env top) a ci
  have hePairs := ForcingOrderedPairForcing.eq_opair_congr hM hpre htW hTop hPair hPair'
    (ForcingAtomicBasic.eq_refl hM hpre a a4 ha4) hjCi
  have hez := ForcingAtomicLaws.eq_trans hM hpre (ForcingAtomicBasic.eq_mono hM hpre ha4 ha4a3 hzPair) hePairs
  have ha4a2 := hpre.2 a4 a3 a2 ha4 ha3 ha2 ha4a3 ha3a2
  have ha4a1 := hpre.2 a4 a2 a1 ha4 ha2 ha1 ha4a2 ha2a1
  have ha4q := hpre.2 a4 a1 q ha4 ha1 hq ha4a1 ha1q
  have hAppS' := app_congr hM hpre ha4 (ForcingAtomicBasic.eq_refl hM hpre (env s) a4 ha4)
    hez (ForcingAtomicBasic.eq_refl hM hpre x a4 ha4)
    (ForcingFormula.mono hM hpre (Source.SetLanguage.edge 0 1 2) (args3 (env s) z x) ha2 ha4 ha4a2 hAppS)
  have hSlice := (ForcingSliceGeometry.slice_force_iff hM env rho G F mul hPres hG hF ht hpre haHS hCiHS hPair' ha4).mpr
    ⟨ForcingAtomicBasic.mem_mono hM hpre ha4 ha4a3 haA,ForcingAtomicBasic.mem_mono hM hpre ha4 ha4a1 hxX,hAppS'⟩
  have hBImage : Force R H env (Fin.lastCases x (four (env s) (env A) (env X) ci)) W a4 ForcingSliceGeometry.bFormula :=
    (ForcingSliceGeometry.b_force_dense hM hpre).mpr (fun d hd hda4 =>
      ⟨d,hd,hpre.1 d hd,a,(domain_semantics env rho G F a).mpr haHS,
        ForcingFormula.mono hM hpre ForcingSliceGeometry.sliceFormula _ ha4 hd hda4 hSlice⟩)
  have hOccForce : Force R H env (Fin.lastCases y (Fin.lastCases ci
      (ForcingMapCalculus.five (env f) (env s) (env A) (env X) (env Y)))) W a4 occurrenceFormula := by
    apply (ForcingSliceGeometry.occurrence_force_dense hM hpre).mpr
    intro d hd hda4
    have hdq := hpre.2 d a4 q hd ha4 hq hda4 ha4q
    have hda1 := hpre.2 d a4 a1 hd ha4 ha1 hda4 ha4a1
    exact ⟨d,hd,hpre.1 d hd,x,hx,ForcingFormula.mono hM hpre ForcingSliceGeometry.bFormula _ ha4 hd hda4 hBImage,
      ForcingAtomicBasic.mem_mono hM hpre hd hdq hyY,
      ForcingFormula.mono hM hpre (Source.SetLanguage.edge 0 1 2) (args3 (env f) x y) ha1 hd hda1 hAppF⟩
  refine ⟨a4,ha4,hpre.2 a4 a1 r ha4 ha1 hr ha4a1 ha1r,i,hi,?_⟩
  apply (ForcingLeastRelation.occurrence_semantics env rho G F mul top (ForcingMapCalculus.five f s A X Y)
    occurrenceFormula a4 y i).mpr
  refine ⟨ci,hCi,?_⟩
  unfold ForcingLeastRelation.values
  rw [five_map]
  exact hOccForce


/-- Binder transport for the SAME source occurrence, with no new forcing
relation and no replacement of the internal index by an external ordinal. -/
theorem occurrence_reindex {k l : Nat} (env : Fin k → M.Carrier .set)
    (other : Fin l → M.Carrier .set) (base : Fin k → Fin l)
    (he : ∀ j, other (base j) = env j) (rho : Fin 7 → Fin k)
    (G F mul top f s A X Y : Fin k) (p x i : M.Carrier .set) :
    Holds (occurrence rho G F mul top f s A X Y) env p x i ↔
      Holds (occurrence (fun j => base (rho j)) (base G) (base F) (base mul) (base top)
        (base f) (base s) (base A) (base X) (base Y)) other p x i := by
  have hR (a b : M.Carrier .set) : MapRel (orderFormula (rho 0) mul) env a b ↔
      MapRel (orderFormula (base (rho 0)) (base mul)) other a b := by
    simp only [orderFormula_semantics,he]
  have hH (a : M.Carrier .set) : Predicate (domain rho G F) env a ↔
      Predicate (domain (fun j => base (rho j)) (base G) (base F)) other a := by
    simp only [domain_semantics,he]
  have hv : (fun j => other (ForcingMapCalculus.five (base f) (base s) (base A) (base X) (base Y) j)) =
      (fun j => env (ForcingMapCalculus.five f s A X Y j)) := by
    simp only [five_map,he]
  simp only [occurrence,ForcingLeastRelation.occurrence_semantics,ForcingLeastRelation.Occurrence,he]
  apply exists_congr
  intro ci
  apply and_congr Iff.rfl
  unfold ForcingLeastRelation.values
  rw [hv]
  simpa only [he] using ForcingSeparation.force_congr hR hH occurrenceFormula
    (Fin.lastCases x (Fin.lastCases ci (fun j => env (ForcingMapCalculus.five f s A X Y j)))) (env (rho 6)) p

theorem at_reindex {k l : Nat} (env : Fin k → M.Carrier .set)
    (other : Fin l → M.Carrier .set) (base : Fin k → Fin l)
    (he : ∀ j, other (base j) = env j) (rho : Fin 7 → Fin k)
    (G F mul top O f s A X Y : Fin k) (p x i : M.Carrier .set) :
    ForcingLeastOccurrence.At (orderFormula (rho 0) mul) (occurrence rho G F mul top f s A X Y)
      env (env (rho 6)) (env O) p x i ↔
    ForcingLeastOccurrence.At (orderFormula (base (rho 0)) (base mul))
      (occurrence (fun j => base (rho j)) (base G) (base F) (base mul) (base top)
        (base f) (base s) (base A) (base X) (base Y)) other (other (base (rho 6))) (other (base O)) p x i := by
  simp only [ForcingLeastOccurrence.At,he,
    ← occurrence_reindex env other base he rho G F mul top f s A X Y,orderFormula_semantics]

/-- The actual raw Ypart selector equation, with its INTERNAL index as a
set parameter. This is not merely an occurrence predicate or membership law. -/
def YName {k : Nat} (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k)
    (G F mul top O f s A X Y : Fin k) (i name : M.Carrier .set) : Prop :=
  HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) name ∧
  ∀ child p, PureKuratowski.PairMember M child p name ↔
    (∃ c, PureKuratowski.PairMember M child c (env Y)) ∧
      (Project.FirstOrderSemantics.reduct M).mem p (env (rho 6)) ∧
      Forces false (orderFormula (rho 0) mul) env (env (rho 6)) child (env Y) p ∧
      ForcingLeastOccurrence.At (orderFormula (rho 0) mul) (occurrence rho G F mul top f s A X Y)
        env (env (rho 6)) (env O) p child i

private theorem yName_from_selected {k l : Nat} (env : Fin k → M.Carrier .set)
    (other : Fin l → M.Carrier .set) (base : Fin k → Fin l)
    (he : ∀ j, other (base j) = env j) (rho : Fin 7 → Fin k)
    (G F mul top O f s A X Y : Fin k) (ii : Fin l) {name : M.Carrier .set}
    (hHS : HS actionFormula (fun j => other (base (rho j))) (other (base G))
      (other (base (rho 6))) (other (base F)) name)
    (hSel : ForcingSliceSelection.Selected (orderFormula (base (rho 0)) (base mul))
      (ForcingSliceGeometry.YPredicate (fun j => base (rho j)) (base G) (base F) (base mul)
        (base top) (base O) (base f) (base s) (base A) (base X) (base Y) ii)
      other (other (base (rho 6))) (other (base Y)) name) :
    YName env rho G F mul top O f s A X Y (other ii) name := by
  refine ⟨?_,?_⟩
  · simpa only [he] using hHS
  · intro child p
    have hR (a b : M.Carrier .set) : MapRel (orderFormula (rho 0) mul) env a b ↔
        MapRel (orderFormula (base (rho 0)) (base mul)) other a b := by
      simp only [orderFormula_semantics,he]
    have hh := hSel child p
    rw [ForcingSliceGeometry.yPredicate_semantics,
      ← at_reindex env other base he rho G F mul top O f s A X Y] at hh
    simpa only [he,← ForcingSeparation.atomic_congr hR false] using hh

/-- Dense coverage by ACTUAL source Ypart names, not just by an abstract
least-index relation. All five parent names and the whole ordinal are internal. -/
def YCover {k : Nat} (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k)
    (G F mul top O f s A X Y p : Fin k) : Prop :=
  ∀ y, Predicate (domain rho G F) env y → ∀ q,
    (Project.FirstOrderSemantics.reduct M).mem q (env (rho 6)) →
    MapRel (orderFormula (rho 0) mul) env q (env p) →
    Forces false (orderFormula (rho 0) mul) env (env (rho 6)) y (env Y) q → ∀ r,
    (Project.FirstOrderSemantics.reduct M).mem r (env (rho 6)) →
    MapRel (orderFormula (rho 0) mul) env r q → ∃ t,
    (Project.FirstOrderSemantics.reduct M).mem t (env (rho 6)) ∧
    MapRel (orderFormula (rho 0) mul) env t r ∧ ∃ i,
    (Project.FirstOrderSemantics.reduct M).mem i (env O) ∧ ∃ name,
    YName env rho G F mul top O f s A X Y i name ∧
    Forces false (orderFormula (rho 0) mul) env (env (rho 6)) y name t

theorem Ypart_cover (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k)
    (I K B w G F mul top s f A X Y O checkedO Cart p : Fin k)
    (hPres : Presentation (env (rho 0)) (env I) (env K) (env B) (env w)
      (env (rho 1)) (env (rho 2)) (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hG : ForcingLabelPermutations.Carrier (env I) (env G))
    (hF : ForcingNormalFilter.Normal (env I) (env G) (env F))
    (ht : ForcingWithTopCarrier.Empty (env top))
    (hpre : ForcingAtomicBasic.PreorderOn (orderFormula (rho 0) mul) env (env (rho 6)))
    (hNames : ∀ j, HS actionFormula (fun a => env (rho a)) (env G) (env (rho 6)) (env F)
      (env (ForcingMapCalculus.five f s A X Y j)))
    (hOrd : ForcingRawRank.Ordinal (env O))
    (hO : ForcingCheckName.Checked (env top) (env O) (env checkedO))
    (hCart : ForcingRelationGraph.Graph (orderFormula (rho 0) mul) ForcingCompletionGraph.trueRelation
      env (rho 6) top A checkedO (env Cart))
    (hp : (Project.FirstOrderSemantics.reduct M).mem (env p) (env (rho 6)))
    (hs : Force (orderFormula (rho 0) mul) (domain rho G F) env (args3 (env s) (env Cart) (env X))
      (env (rho 6)) (env p) (Source.SetLanguage.surjection 0 1 2))
    (hf : Force (orderFormula (rho 0) mul) (domain rho G F) env (args3 (env f) (env X) (env Y))
      (env (rho 6)) (env p) (Source.SetLanguage.surjection 0 1 2)) :
    YCover env rho G F mul top O f s A X Y p := by
  have hA : HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) (env A) := by
    simpa only [ForcingMapCalculus.five,args3,Fin.cases_zero,Fin.cases_succ] using hNames (Fin.succ (Fin.succ 0))
  have hY : HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) (env Y) := by
    simpa only [ForcingMapCalculus.five,args3,args2,args1,Fin.cases_zero,Fin.cases_succ]
      using hNames (Fin.succ (Fin.succ (Fin.succ (Fin.succ 0))))
  have hCover := occurrence_cover hM env rho I K B w G F mul top s f A X Y O checkedO Cart p
    hPres hG hF ht hpre hA hO hCart hp hs hf
  obtain ⟨S,_hS,_hSF,_hFixed,hParts⟩ := ForcingSliceGeometry.construct_family hM env rho I K B w G F mul top O f s A X Y
    hPres hG hF ht hNames
  intro y hy q hq hqp hyY r hr hrq
  obtain ⟨t,ht, htr,i,hAt⟩ := ForcingLeastOccurrence.dense hM (orderFormula (rho 0) mul)
    (occurrence rho G F mul top f s A X Y) env (env (rho 6)) (env O) q y hOrd hpre (hCover y hy q hq hqp hyY) r hr hrq
  obtain ⟨ci,_hCi,Bi,Yi,Si,_hBi,_hFixBi,_hB,hYi,_hFixYi,hYP,_hSi,_hFixSi,_hSP⟩ := hParts i hAt.1
  let ext : Fin (k+3) → M.Carrier .set := Fin.lastCases ci (Fin.lastCases i (Fin.lastCases S env))
  let up (a : Fin k) : Fin (k+3) := a.castSucc.castSucc.castSucc
  let rr : Fin 7 → Fin (k+3) := fun a => up (rho a)
  let ii : Fin (k+3) := (Fin.last (k+1)).castSucc
  have eu (a : Fin k) : ext (up a) = env a := by simp only [ext,up,Fin.lastCases_castSucc]
  have ei : ext ii = i := by simp only [ext,ii,Fin.lastCases_castSucc,Fin.lastCases_last]
  have hR (a b : M.Carrier .set) : MapRel (orderFormula (rho 0) mul) env a b ↔
      MapRel (orderFormula (rr 0) (up mul)) ext a b := by simp only [orderFormula_semantics,rr,eu]
  have hpre' : ForcingAtomicBasic.PreorderOn (orderFormula (rr 0) (up mul)) ext (ext (rr 6)) := by
    simpa only [ForcingAtomicBasic.PreorderOn,rr,eu,← hR] using hpre
  have hAt' := (at_reindex env ext up eu rho G F mul top O f s A X Y t y i).mp hAt
  have hy' : Predicate (domain rr (up G) (up F)) ext y := by
    simpa only [domain_semantics,rr,eu] using hy
  have hY' : HS actionFormula (fun j => ext (rr j)) (ext (up G)) (ext (rr 6)) (ext (up F)) (ext (up Y)) := by
    simpa only [rr,eu] using hY
  have ht' : (Project.FirstOrderSemantics.reduct M).mem t (ext (rr 6)) := by simpa only [rr,eu] using ht
  have hyY' : Forces false (orderFormula (rr 0) (up mul)) ext (ext (rr 6)) y (ext (up Y)) t := by
    simpa only [rr,eu] using (ForcingSeparation.atomic_congr hR false (env (rho 6)) y (env Y) t).mp
      (ForcingAtomicBasic.mem_mono hM hpre ht (hpre.2 t r q ht hr hq htr hrq) hyY)
  have hMember := (ForcingSliceGeometry.mem_Ypart hM ext rr (up G) (up F) (up mul) (up top) (up O)
    (up f) (up s) (up A) (up X) (up Y) ii hpre' hY' hy' hYP ht').mpr ⟨hyY',by simpa only [ei] using hAt'⟩
  have hName := yName_from_selected env ext up eu rho G F mul top O f s A X Y ii hYi hYP
  refine ⟨t,ht,htr,i,hAt.1,Yi,?_,?_⟩
  · simpa only [ei] using hName
  · apply (ForcingSeparation.atomic_congr hR false (env (rho 6)) y Yi t).mpr
    simpa only [rr,eu] using hMember


def yName {k m : Nat} (rho : Fin 7 → Fin k) (G F mul top O f s A X Y : Fin k)
    (base : Fin k → Fin m) (i name : Fin m) : Formula m :=
  let b : Fin k → Fin (m+2) := fun j => (base j).castSucc.castSucc
  let child := (Fin.last m).castSucc
  let p := Fin.last (m+1)
  (ForcingHS.hs actionFormula (fun j => base (rho j)) (base G) (base (rho 6)) (base F) name).conj
    (.all (.all ((Source.SetLanguage.edge name.castSucc.castSucc child p).iff
      ((Formula.ex (Source.SetLanguage.edge (base Y).castSucc.castSucc.castSucc child.castSucc (Fin.last (m+2)))).conj
        ((Formula.mem p (b (rho 6))).conj
          ((ForcingAtomicRelations.forces false (orderFormula (rho 0) mul) b (b (rho 6)) child (b Y) p).conj
            (ForcingLeastOccurrence.atFormula (orderFormula (rho 0) mul) (occurrence rho G F mul top f s A X Y)
              b (b (rho 6)) (b O) p child i.castSucc.castSucc)))))))

theorem yName_semantics {k m : Nat} (v : Fin m → M.Carrier .set) (rho : Fin 7 → Fin k)
    (G F mul top O f s A X Y : Fin k) (base : Fin k → Fin m) (i name : Fin m) :
    Formula.Realize (Project.FirstOrderSemantics.reduct M).mem v (yName rho G F mul top O f s A X Y base i name) ↔
      YName (fun j => v (base j)) rho G F mul top O f s A X Y (v i) (v name) := by
  simp only [yName,YName,Source.Formula.iff,Formula.Realize,ForcingHS.hs_semantics,KuratowskiZF.source_edge,
    ForcingAtomicRelations.forces_semantics,ForcingLeastOccurrence.at_semantics,
    Fin.lastCases_last,Fin.lastCases_castSucc]
  exact and_congr Iff.rfl ⟨fun h x p => ⟨(h x p).1,(h x p).2⟩,fun h x p => ⟨(h x p).mp,(h x p).mpr⟩⟩

/-- The source dense-cover combinator is reused verbatim. Its final witness
is now the actual selected Ypart NAME, not an unchecked occurrence oracle. -/
def yLocated {k : Nat} (rho : Fin 7 → Fin k) (G F mul top O f s A X Y : Fin k) : Formula (k+3) :=
  let b : Fin k → Fin (k+4) := fun j => j.castSucc.castSucc.castSucc.castSucc
  let p := (Fin.last k).castSucc.castSucc.castSucc
  let y := (Fin.last (k+1)).castSucc.castSucc
  let i := (Fin.last (k+2)).castSucc
  let name := Fin.last (k+3)
  .ex ((yName rho G F mul top O f s A X Y b i name).conj
    (ForcingAtomicRelations.forces false (orderFormula (rho 0) mul) b (b (rho 6)) y name p))

theorem yLocated_semantics {k : Nat} (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k)
    (G F mul top O f s A X Y : Fin k) (p y i : M.Carrier .set) :
    Holds (yLocated rho G F mul top O f s A X Y) env p y i ↔ ∃ name,
      YName env rho G F mul top O f s A X Y i name ∧
      Forces false (orderFormula (rho 0) mul) env (env (rho 6)) y name p := by
  simp only [Holds,yLocated,Formula.Realize,yName_semantics,ForcingAtomicRelations.forces_semantics,
    Fin.lastCases_last,Fin.lastCases_castSucc]
  rfl

def yCovering {k : Nat} (rho : Fin 7 → Fin k) (G F mul top O f s A X Y p : Fin k) : Formula k :=
  ForcingLeastRelation.covering (orderFormula (rho 0) mul) (yLocated rho G F mul top O f s A X Y)
    (domain rho G F) id (rho 6) O Y p

theorem yCovering_semantics {k : Nat} (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k)
    (G F mul top O f s A X Y p : Fin k) :
    Formula.Realize (Project.FirstOrderSemantics.reduct M).mem env (yCovering rho G F mul top O f s A X Y p) ↔
      YCover env rho G F mul top O f s A X Y p := by
  rw [yCovering,ForcingLeastRelation.covering_semantics]
  simp only [ForcingLeastRelation.Cover,ForcingLeastOccurrence.Dense,yLocated_semantics,id_eq,YCover]
  rfl


def occurrenceSentence {k : Nat} (rho : Fin 7 → Fin k) (I K B w G F mul top s f A X Y O checkedO Cart p : Fin k) : Project.Sentence where
  formula := Project.Formula.forallClosure k
    ([ProjectSyntax.encode id (ForcingProductFamily.presentation (rho 0) I K B w (rho 1) (rho 2) (rho 3) (rho 4) (rho 5) (rho 6)),
      ProjectSyntax.encode id (ForcingLabelPermutations.carrier I G),
      ProjectSyntax.encode id (ForcingNormalFilter.normal I G F),
      ProjectSyntax.encode id (ForcingWithTopCarrier.empty top),
      ProjectSyntax.encode id (ForcingAtomicBasic.preorder (orderFormula (rho 0) mul) id (rho 6)),
      ProjectSyntax.encode id (ForcingHS.hs actionFormula rho G (rho 6) F A),
      ProjectSyntax.encode id (ForcingCheckName.checkName top O checkedO),
      ProjectSyntax.encode id (ForcingRelationGraph.graph (orderFormula (rho 0) mul) ForcingCompletionGraph.trueRelation id (rho 6) top A checkedO Cart),
      .mem (.bound p) (.bound (rho 6)),
      ProjectSyntax.encode id (ForcingFormula.formula (orderFormula (rho 0) mul) (domain rho G F) id (args3 s Cart X) (rho 6) p (Source.SetLanguage.surjection 0 1 2)),
      ProjectSyntax.encode id (ForcingFormula.formula (orderFormula (rho 0) mul) (domain rho G F) id (args3 f X Y) (rho 6) p (Source.SetLanguage.surjection 0 1 2))].foldr Definitional.Formula.imp
      (ProjectSyntax.encode id (ForcingLeastRelation.covering (orderFormula (rho 0) mul) (occurrence rho G F mul top f s A X Y) (domain rho G F) id (rho 6) O Y p)))
  freeClosed := by simp -implicitDefEqProofs [List.foldr,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed]

theorem occurrence_models {k : Nat} (rho : Fin 7 → Fin k) (I K B w G F mul top s f A X Y O checkedO Cart p : Fin k)
    (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (occurrenceSentence rho I K B w G F mul top s f A X Y O checkedO Cart p)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM),SetTheory.Structure.satisfiesSentence_iff]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro env
  simp only [List.foldr,Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingProductFamily.presentation_semantics,ForcingLabelPermutations.carrier_semantics,
    ForcingNormalFilter.normal_semantics,ForcingWithTopCarrier.empty_semantics,ForcingAtomicBasic.preorder_semantics,
    ForcingHS.hs_semantics,ForcingCheckName.checkName_semantics,
    ForcingRelationGraph.graph_semantics,ForcingFormula.formula_semantics,ForcingLeastRelation.covering_semantics,
    id_eq]
  exact occurrence_cover hM env rho I K B w G F mul top s f A X Y O checkedO Cart p

theorem occurrence_kernel_certificate {k : Nat} (rho : Fin 7 → Fin k) (I K B w G F mul top s f A X Y O checkedO Cart p : Fin k) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (occurrenceSentence rho I K B w G F mul top s f A X Y O checkedO Cart p)) :=
  ModelTransfer.derives (fun _ hM => occurrence_models rho I K B w G F mul top s f A X Y O checkedO Cart p hM)

def yCoverSentence {k : Nat} (rho : Fin 7 → Fin k) (I K B w G F mul top s f A X Y O checkedO Cart p : Fin k) : Project.Sentence where
  formula := Project.Formula.forallClosure k
    ([ProjectSyntax.encode id (ForcingProductFamily.presentation (rho 0) I K B w (rho 1) (rho 2) (rho 3) (rho 4) (rho 5) (rho 6)),
      ProjectSyntax.encode id (ForcingLabelPermutations.carrier I G),
      ProjectSyntax.encode id (ForcingNormalFilter.normal I G F),
      ProjectSyntax.encode id (ForcingWithTopCarrier.empty top),
      ProjectSyntax.encode id (ForcingAtomicBasic.preorder (orderFormula (rho 0) mul) id (rho 6)),
      ProjectSyntax.encode id (ForcingHS.hs actionFormula rho G (rho 6) F f),
      ProjectSyntax.encode id (ForcingHS.hs actionFormula rho G (rho 6) F s),
      ProjectSyntax.encode id (ForcingHS.hs actionFormula rho G (rho 6) F A),
      ProjectSyntax.encode id (ForcingHS.hs actionFormula rho G (rho 6) F X),
      ProjectSyntax.encode id (ForcingHS.hs actionFormula rho G (rho 6) F Y),
      ProjectSyntax.encode id (OrdinalSyntax.ordinal O),
      ProjectSyntax.encode id (ForcingCheckName.checkName top O checkedO),
      ProjectSyntax.encode id (ForcingRelationGraph.graph (orderFormula (rho 0) mul) ForcingCompletionGraph.trueRelation id (rho 6) top A checkedO Cart),
      .mem (.bound p) (.bound (rho 6)),
      ProjectSyntax.encode id (ForcingFormula.formula (orderFormula (rho 0) mul) (domain rho G F) id (args3 s Cart X) (rho 6) p (Source.SetLanguage.surjection 0 1 2)),
      ProjectSyntax.encode id (ForcingFormula.formula (orderFormula (rho 0) mul) (domain rho G F) id (args3 f X Y) (rho 6) p (Source.SetLanguage.surjection 0 1 2))].foldr Definitional.Formula.imp
      (ProjectSyntax.encode id (yCovering rho G F mul top O f s A X Y p)))
  freeClosed := by simp -implicitDefEqProofs [List.foldr,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed]

theorem yCover_models {k : Nat} (rho : Fin 7 → Fin k) (I K B w G F mul top s f A X Y O checkedO Cart p : Fin k)
    (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (yCoverSentence rho I K B w G F mul top s f A X Y O checkedO Cart p)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM),SetTheory.Structure.satisfiesSentence_iff]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro env
  simp only [List.foldr,Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingProductFamily.presentation_semantics,ForcingLabelPermutations.carrier_semantics,
    ForcingNormalFilter.normal_semantics,ForcingWithTopCarrier.empty_semantics,ForcingAtomicBasic.preorder_semantics,
    ForcingHS.hs_semantics,ForcingRawRank.ordinal_semantics,ForcingCheckName.checkName_semantics,
    ForcingRelationGraph.graph_semantics,ForcingFormula.formula_semantics,
    yCovering_semantics,id_eq]
  intro hPres hG hF ht hpre hfHS hsHS hA hX hY hOrd hO hCart hp hs hf
  apply Ypart_cover hM env rho I K B w G F mul top s f A X Y O checkedO Cart p hPres hG hF ht hpre ?_ hOrd hO hCart hp hs hf
  intro j
  exact Fin.cases hfHS (Fin.cases hsHS (Fin.cases hA (Fin.cases hX (Fin.cases hY (fun a => Fin.elim0 a))))) j

theorem yCover_kernel_certificate {k : Nat} (rho : Fin 7 → Fin k) (I K B w G F mul top s f A X Y O checkedO Cart p : Fin k) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (yCoverSentence rho I K B w G F mul top s f A X Y O checkedO Cart p)) :=
  ModelTransfer.derives (fun _ hM => yCover_models rho I K B w G F mul top s f A X Y O checkedO Cart p hM)

end PPAC.Migration.ForcingSliceCoverage
