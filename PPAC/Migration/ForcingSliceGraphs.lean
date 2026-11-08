/- Pinned SliceGeometry.sliceGraph_surjection/partGraph_surjection:249-295.
Construct the actual supported graphs with the EXISTING collector and prove
FULL source surjections, including functionOn/no junk. Uniqueness is used
only on the original source domains. -/
import PPAC.Migration.ForcingSliceGeometry
import PPAC.Migration.ForcingCompletionGraph

namespace PPAC.Migration.ForcingSliceGraphs
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open Source (Formula)
open Source.SetLanguage (args2 args3)
open ForcingMapConditions (MapRel)
open ForcingAtomicRelations (Forces)
open ForcingFormula (Force)
open ForcingClassEvaluation (Predicate)
open ForcingProductFamily (Presentation actionFormula mapRel_action)
open ForcingProductSymmetry (orderFormula orderFormula_semantics)
open ForcingPairUnion (domain domain_semantics)
open ForcingHS (HS)
open ForcingSupportedNames (Supported)
open ForcingRelationGraphForcing (Holds)
open ForcingSliceGeometry (four sliceFormula BPredicate)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 400000
universe u v
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

private theorem four_map {a : Type v} {b : Type u} (g : a → b) (s A X ci : a) :
    (fun j => g (four s A X ci j)) = four (g s) (g A) (g X) (g ci) := by
  funext j
  exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun t => Fin.elim0 t)))) j

def sliceRelation {k : Nat} (rho : Fin 7 → Fin k) (G F mul s A X ci : Fin k) : Formula (k+3) :=
  ForcingMapCalculus.relationOf rho G F mul (four s A X ci) sliceFormula

theorem slice_semantics {k : Nat} (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k)
    (G F mul s A X ci : Fin k) (p a x : M.Carrier .set) :
    Holds (sliceRelation rho G F mul s A X ci) env p a x ↔
      Force (orderFormula (rho 0) mul) (domain rho G F) env
        (Fin.lastCases x (Fin.lastCases a (four (env s) (env A) (env X) (env ci)))) (env (rho 6)) p sliceFormula := by
  rw [sliceRelation,ForcingMapCalculus.relationOf_semantics,four_map]

theorem B_subset (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (G F mul s A X ci Bi : Fin k)
    {nu p : M.Carrier .set}
    (hpre : ForcingAtomicBasic.PreorderOn (orderFormula (rho 0) mul) env (env (rho 6)))
    (hX : HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) (env X))
    (hNu : Predicate (domain rho G F) env nu)
    (hB : ForcingSliceSelection.Selected (orderFormula (rho 0) mul) (BPredicate rho G F mul s A X ci)
      env (env (rho 6)) (env X) (env Bi))
    (hp : (Project.FirstOrderSemantics.reduct M).mem p (env (rho 6)))
    (hMem : Forces false (orderFormula (rho 0) mul) env (env (rho 6)) nu (env Bi) p) :
    Forces false (orderFormula (rho 0) mul) env (env (rho 6)) nu (env X) p :=
  ((ForcingSliceGeometry.mem_formula_selection hM env rho G F mul X (four s A X ci)
    ForcingSliceGeometry.bFormula hpre hX hNu hB hp).mp hMem).1

/-- The actual i-th slice graph, under EXACTLY the source mapsTo premise
for s. No surjectivity of the whole presentation is required here. -/
theorem sliceGraph_surjection (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k)
    (I K B w G F S mul top s A X O checkedO i ci Bi Cart p : Fin k)
    (hPres : Presentation (env (rho 0)) (env I) (env K) (env B) (env w)
      (env (rho 1)) (env (rho 2)) (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hG : ForcingLabelPermutations.Carrier (env I) (env G))
    (hF : ForcingNormalFilter.Normal (env I) (env G) (env F))
    (hS : ForcingConjugationGraph.Subgroup (env I) (env G) (env S))
    (hSF : (Project.FirstOrderSemantics.reduct M).mem (env S) (env F))
    (ht : ForcingWithTopCarrier.Empty (env top))
    (hpre : ForcingAtomicBasic.PreorderOn (orderFormula (rho 0) mul) env (env (rho 6)))
    (hA : HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) (env A))
    (hX : HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) (env X))
    (hBi : HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) (env Bi))
    (hFixs : Supported (fun j => env (rho j)) (env S) (env s))
    (hFixA : Supported (fun j => env (rho j)) (env S) (env A))
    (hFixX : Supported (fun j => env (rho j)) (env S) (env X))
    (hFixBi : Supported (fun j => env (rho j)) (env S) (env Bi))
    (hO : ForcingCheckName.Checked (env top) (env O) (env checkedO))
    (hi : (Project.FirstOrderSemantics.reduct M).mem (env i) (env O))
    (hCi : ForcingCheckName.Checked (env top) (env i) (env ci))
    (hB : ForcingSliceSelection.Selected (orderFormula (rho 0) mul) (BPredicate rho G F mul s A X ci)
      env (env (rho 6)) (env X) (env Bi))
    (hCart : ForcingRelationGraph.Graph (orderFormula (rho 0) mul) ForcingCompletionGraph.trueRelation
      env (rho 6) top A checkedO (env Cart))
    (hp : (Project.FirstOrderSemantics.reduct M).mem (env p) (env (rho 6)))
    (hs : Force (orderFormula (rho 0) mul) (domain rho G F) env (args3 (env s) (env Cart) (env X))
      (env (rho 6)) (env p) (Source.SetLanguage.mapsTo 0 1 2)) :
    ∃ graph, ForcingRelationGraph.Graph (orderFormula (rho 0) mul) (sliceRelation rho G F mul s A X ci)
      env (rho 6) top A Bi graph ∧
      HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) graph ∧
      Supported (fun j => env (rho j)) (env S) graph ∧
      Force (orderFormula (rho 0) mul) (domain rho G F) env (args3 graph (env A) (env Bi))
        (env (rho 6)) (env p) (Source.SetLanguage.surjection 0 1 2) := by
  let R := orderFormula (rho 0) mul
  let H := domain rho G F
  let W := env (rho 6)
  let Q := sliceRelation rho G F mul s A X ci
  let v7 : Fin 7 → M.Carrier .set := fun j => env (rho j)
  have hCheckOHS := ForcingSectionInjection.checked_hs hM v7 hPres hG hF ht hO
  have hCiHS := ForcingSectionInjection.checked_hs hM v7 hPres hG hF ht hCi
  have hFixCi : Supported v7 (env S) (env ci) := by
    intro pi _hpi act hAct
    exact ForcingLabelNames.checked_fixed hM v7 hPres ht ((mapRel_action _ _ _).mp hAct) hCi
  have hFixed (j : Fin 4) : Supported v7 (env S) (env (four s A X ci j)) :=
    Fin.cases hFixs (Fin.cases hFixA (Fin.cases hFixX (Fin.cases hFixCi (fun t => Fin.elim0 t)))) j
  have hMove : ForcingRelationGraphSupport.Moves Q env rho G F S := by
    intro pi hpi act hAct a b x y x' y' ha hab _hx _hy hxx hyy hRel
    exact ForcingMapCalculus.move hM env rho G F mul (four s A X ci) sliceFormula hPres hG hF
      ((hG pi).mp (hS.1 pi hpi)) hAct (fun j => hFixed j pi hpi act hAct) ha hab hxx hyy hRel
  obtain ⟨graph,hGraph,hGraphHS,hGraphFix⟩ := ForcingRelationGraphSupport.construct hM Q env rho
    I K B w G F S mul top A Bi hPres hG hF hS ht hA hBi hFixA hFixBi hMove hSF
  have hMono := ForcingMapCalculus.monotone hM env rho G F mul (four s A X ci) sliceFormula hpre
  have hCongr := ForcingMapCalculus.congruent hM env rho G F mul (four s A X ci) sliceFormula hpre
  have hRegular := ForcingMapCalculus.regular hM env rho G F mul (four s A X ci) sliceFormula hpre
  have hDomain (x : M.Carrier .set)
      (hx : HS (ForcingRelationGraphApplication.actionAt rho) env (env G) W (env F) x) : Predicate H env x :=
    (domain_semantics env rho G F x).mpr ((ForcingRelationGraphApplication.hs_actionAt env rho _ _ _ _).mp hx)
  have htW := (hPres.2.2.2.2.2 (env top)).mpr (Or.inl ht)
  have hTop : ∀ a, (Project.FirstOrderSemantics.reduct M).mem a W → MapRel R env a (env top) :=
    fun a _ => (orderFormula_semantics env (rho 0) mul a (env top)).mpr (Or.inl ht)
  have hCiMem (q : M.Carrier .set) (hq : (Project.FirstOrderSemantics.reduct M).mem q W) :=
    ForcingInfinity.check_mem_of_mem hM hpre hO hCi hi htW hTop hq
  refine ⟨graph,hGraph,hGraphHS,hGraphFix,?_⟩
  apply ForcingRelationGraphFunctions.graph_surjection hM env rho G F mul top A Bi Q
    (args3 graph (env A) (env Bi)) 0 1 2 hPres hG hF ht hpre hA hBi
    hMono hCongr hRegular hGraph rfl rfl ?_ ?_ ?_ hp
  · intro a ha q hq hqp haA r hr hrq
    have haHS := (domain_semantics env rho G F a).mp (hDomain a ha)
    obtain ⟨pair,hPair⟩ := ForcingOrderedPairName.exists_orderedPairName hM (env top) a (env ci)
    have hPairHS := ForcingOrderedPairName.orderedPair_hs hM v7 hPres hG hF ht haHS hCiHS hPair
    have hCartMem := (ForcingCompletionGraph.cartesian_pair_mem hM env rho G F mul top A checkedO
      hPres ht hpre hA hCheckOHS hCart haHS hCiHS hPair hq).mpr ⟨haA,hCiMem q hq⟩
    obtain ⟨t,htP,htr,x,hx,hxX,hApp⟩ := ForcingImageQuotient.mapsTo_total_reuse hM hpre hp hs
      ((domain_semantics env rho G F pair).mpr hPairHS) hq hqp hCartMem hr hrq
    have htq := hpre.2 t r q htP hr hq htr hrq
    have hSlice := (ForcingSliceGeometry.slice_force_iff hM env rho G F mul hPres hG hF ht hpre haHS hCiHS hPair htP).mpr
      ⟨ForcingAtomicBasic.mem_mono hM hpre htP htq haA,hxX,hApp⟩
    have hxB := (ForcingSliceGeometry.mem_B hM env rho G F mul s A X ci hpre hX hx hB htP).mpr
      ((ForcingSliceGeometry.b_force_dense hM hpre).mpr (fun b hb hbt =>
        ⟨b,hb,hpre.1 b hb,a,hDomain a ha,ForcingFormula.mono hM hpre sliceFormula _ htP hb hbt hSlice⟩))
    exact ⟨t,htP,htr,x,(ForcingRelationGraphApplication.hs_actionAt env rho _ _ _ _).mpr
      ((domain_semantics env rho G F x).mp hx),hxB,(slice_semantics env rho G F mul s A X ci t a x).mpr hSlice⟩
  · intro q hq hqp a x y ha hx hy hRel hRel'
    have haHS := (domain_semantics env rho G F a).mp (hDomain a ha)
    obtain ⟨pair,hPair⟩ := ForcingOrderedPairName.exists_orderedPairName hM (env top) a (env ci)
    have hPairHS := ForcingOrderedPairName.orderedPair_hs hM v7 hPres hG hF ht haHS hCiHS hPair
    have hLeft := (ForcingSliceGeometry.slice_force_iff hM env rho G F mul hPres hG hF ht hpre haHS hCiHS hPair hq).mp
      ((slice_semantics env rho G F mul s A X ci q a x).mp hRel)
    have hRight := (ForcingSliceGeometry.slice_force_iff hM env rho G F mul hPres hG hF ht hpre haHS hCiHS hPair hq).mp
      ((slice_semantics env rho G F mul s A X ci q a y).mp hRel')
    have hCartMem := (ForcingCompletionGraph.cartesian_pair_mem hM env rho G F mul top A checkedO
      hPres ht hpre hA hCheckOHS hCart haHS hCiHS hPair hq).mpr ⟨hLeft.1,hCiMem q hq⟩
    exact ForcingKernelImage.mapsTo_unique_reuse hM hpre hp hq hqp hs
      ((domain_semantics env rho G F pair).mpr hPairHS) (hDomain x hx) (hDomain y hy)
      hCartMem hLeft.2.2 hRight.2.2
  · intro x hx q hq _hqp hxB r hr hrq
    have hImage := (ForcingSliceGeometry.mem_B hM env rho G F mul s A X ci hpre hX (hDomain x hx) hB hq).mp hxB
    obtain ⟨t,htP,htr,a,ha,hSlice⟩ := (ForcingSliceGeometry.b_force_dense hM hpre).mp hImage r hr hrq
    have haA : Forces false R env W a (env A) t := by
      change Forces false R env W a (env A) t ∧ _ at hSlice
      exact hSlice.1
    exact ⟨t,htP,htr,a,(ForcingRelationGraphApplication.hs_actionAt env rho _ _ _ _).mpr
      ((domain_semantics env rho G F a).mp ha),haA,(slice_semantics env rho G F mul s A X ci t a x).mpr hSlice⟩

private theorem args3_map {a : Type v} {b : Type u} (g : a → b) (f X Y : a) :
    (fun j => g (args3 f X Y j)) = args3 (g f) (g X) (g Y) := by
  funext j
  exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun t => Fin.elim0 t))) j

/-- The exact source boundedApp f Spart Ypart. -/
def boundedFormula : Formula 5 :=
  (Formula.mem 3 1).conj ((Formula.mem 4 2).conj (Source.SetLanguage.edge 0 3 4))

def partRelation {k : Nat} (rho : Fin 7 → Fin k) (G F mul f Si Yi : Fin k) : Formula (k+3) :=
  ForcingMapCalculus.relationOf rho G F mul (args3 f Si Yi) boundedFormula

theorem part_semantics (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (G F mul f Si Yi : Fin k)
    {p x y : M.Carrier .set}
    (hpre : ForcingAtomicBasic.PreorderOn (orderFormula (rho 0) mul) env (env (rho 6)))
    (hp : (Project.FirstOrderSemantics.reduct M).mem p (env (rho 6))) :
    Holds (partRelation rho G F mul f Si Yi) env p x y ↔
      Forces false (orderFormula (rho 0) mul) env (env (rho 6)) x (env Si) p ∧
        Forces false (orderFormula (rho 0) mul) env (env (rho 6)) y (env Yi) p ∧
        Force (orderFormula (rho 0) mul) (domain rho G F) env (args3 (env f) x y)
          (env (rho 6)) p (Source.SetLanguage.edge 0 1 2) := by
  rw [partRelation,ForcingMapCalculus.relationOf_semantics,args3_map]
  let vv : Fin 5 → M.Carrier .set := Fin.lastCases y (Fin.lastCases x (args3 (env f) (env Si) (env Yi)))
  change (_ ∧ _ ∧ Force (orderFormula (rho 0) mul) (domain rho G F) env vv (env (rho 6)) p
    (Source.SetLanguage.edge 0 3 4)) ↔ _
  have e0 : vv 0 = env f := by rfl
  have e3 : vv 3 = x := by simp only [vv,show (3 : Fin 5) = (Fin.last 3).castSucc from rfl,Fin.lastCases_last,Fin.lastCases_castSucc]
  have e4 : vv 4 = y := by simp only [vv,show (4 : Fin 5) = Fin.last 4 from rfl,Fin.lastCases_last]
  refine and_congr Iff.rfl (and_congr Iff.rfl ?_)
  simpa only [e0,e3,e4] using ForcingRelationClass.edge_formula (H := domain rho G F) (n := 5) hM hpre hp vv (0 : Fin 5) 3 4

/-- Source restriction graph is actually collected. Totality and onto use
the already constructed piece equations; unique values use ONLY f on X. -/
theorem partGraph_surjection (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k)
    (I K B w G F S mul top O f s A X Y i ci Bi Yi Si p : Fin k)
    (hPres : Presentation (env (rho 0)) (env I) (env K) (env B) (env w)
      (env (rho 1)) (env (rho 2)) (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hG : ForcingLabelPermutations.Carrier (env I) (env G))
    (hF : ForcingNormalFilter.Normal (env I) (env G) (env F))
    (hS : ForcingConjugationGraph.Subgroup (env I) (env G) (env S))
    (hSF : (Project.FirstOrderSemantics.reduct M).mem (env S) (env F))
    (ht : ForcingWithTopCarrier.Empty (env top))
    (hpre : ForcingAtomicBasic.PreorderOn (orderFormula (rho 0) mul) env (env (rho 6)))
    (hX : HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) (env X))
    (hY : HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) (env Y))
    (hYi : HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) (env Yi))
    (hSi : HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) (env Si))
    (hFixf : Supported (fun j => env (rho j)) (env S) (env f))
    (hFixYi : Supported (fun j => env (rho j)) (env S) (env Yi))
    (hFixSi : Supported (fun j => env (rho j)) (env S) (env Si))
    (hCi : ForcingCheckName.Checked (env top) (env i) (env ci))
    (hB : ForcingSliceSelection.Selected (orderFormula (rho 0) mul) (BPredicate rho G F mul s A X ci)
      env (env (rho 6)) (env X) (env Bi))
    (hYP : ForcingSliceSelection.Selected (orderFormula (rho 0) mul) (ForcingSliceGeometry.YPredicate rho G F mul top O f s A X Y i)
      env (env (rho 6)) (env Y) (env Yi))
    (hSP : ForcingSeparation.Separated (orderFormula (rho 0) mul) (domain rho G F) env
      (args3 (env f) (env Bi) (env Yi)) (env (rho 6)) (env Bi) (env Si) ForcingSliceGeometry.preimageFormula)
    (hp : (Project.FirstOrderSemantics.reduct M).mem (env p) (env (rho 6)))
    (hf : Force (orderFormula (rho 0) mul) (domain rho G F) env (args3 (env f) (env X) (env Y))
      (env (rho 6)) (env p) (Source.SetLanguage.mapsTo 0 1 2)) :
    ∃ graph, ForcingRelationGraph.Graph (orderFormula (rho 0) mul) (partRelation rho G F mul f Si Yi)
      env (rho 6) top Si Yi graph ∧
      HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) graph ∧
      Supported (fun j => env (rho j)) (env S) graph ∧
      Force (orderFormula (rho 0) mul) (domain rho G F) env (args3 graph (env Si) (env Yi))
        (env (rho 6)) (env p) (Source.SetLanguage.surjection 0 1 2) := by
  let R := orderFormula (rho 0) mul
  let H := domain rho G F
  let W := env (rho 6)
  let Q := partRelation rho G F mul f Si Yi
  have hFixed (j : Fin 3) : Supported (fun a => env (rho a)) (env S) (env (args3 f Si Yi j)) :=
    Fin.cases hFixf (Fin.cases hFixSi (Fin.cases hFixYi (fun a => Fin.elim0 a))) j
  have hMove : ForcingRelationGraphSupport.Moves Q env rho G F S := by
    intro pi hpi act hAct a b x y x' y' ha hab _hx _hy hxx hyy hRel
    exact ForcingMapCalculus.move hM env rho G F mul (args3 f Si Yi) boundedFormula hPres hG hF
      ((hG pi).mp (hS.1 pi hpi)) hAct (fun j => hFixed j pi hpi act hAct) ha hab hxx hyy hRel
  obtain ⟨graph,hGraph,hGraphHS,hGraphFix⟩ := ForcingRelationGraphSupport.construct hM Q env rho
    I K B w G F S mul top Si Yi hPres hG hF hS ht hSi hYi hFixSi hFixYi hMove hSF
  have hMono := ForcingMapCalculus.monotone hM env rho G F mul (args3 f Si Yi) boundedFormula hpre
  have hCongr := ForcingMapCalculus.congruent hM env rho G F mul (args3 f Si Yi) boundedFormula hpre
  have hRegular := ForcingMapCalculus.regular hM env rho G F mul (args3 f Si Yi) boundedFormula hpre
  have hDomain (x : M.Carrier .set)
      (hx : HS (ForcingRelationGraphApplication.actionAt rho) env (env G) W (env F) x) : Predicate H env x :=
    (domain_semantics env rho G F x).mpr ((ForcingRelationGraphApplication.hs_actionAt env rho _ _ _ _).mp hx)
  refine ⟨graph,hGraph,hGraphHS,hGraphFix,?_⟩
  apply ForcingRelationGraphFunctions.graph_surjection hM env rho G F mul top Si Yi Q
    (args3 graph (env Si) (env Yi)) 0 1 2 hPres hG hF ht hpre hSi hYi hMono hCongr hRegular hGraph rfl rfl ?_ ?_ ?_ hp
  · intro x hx q hq _hqp hxSi r hr hrq
    obtain ⟨t,htP,htr,y,hy,_hxBi,hyYi,hApp⟩ := ((ForcingSliceGeometry.mem_Spart hM hpre hSP hq).mp hxSi).2 r hr hrq
    have htq := hpre.2 t r q htP hr hq htr hrq
    have hxSi' := ForcingAtomicBasic.mem_mono hM hpre htP htq hxSi
    exact ⟨t,htP,htr,y,(ForcingRelationGraphApplication.hs_actionAt env rho _ _ _ _).mpr
      ((domain_semantics env rho G F y).mp hy),hyYi,
      (part_semantics hM env rho G F mul f Si Yi hpre htP).mpr ⟨hxSi',hyYi,hApp⟩⟩
  · intro q hq hqp x y z hx hy hz hRel hRel'
    obtain ⟨hxSi,_hyYi,hAppY⟩ := (part_semantics hM env rho G F mul f Si Yi hpre hq).mp hRel
    obtain ⟨_,_hzYi,hAppZ⟩ := (part_semantics hM env rho G F mul f Si Yi hpre hq).mp hRel'
    have hxBi := ((ForcingSliceGeometry.mem_Spart hM hpre hSP hq).mp hxSi).1
    have hxX := B_subset hM env rho G F mul s A X ci Bi hpre hX (hDomain x hx) hB hq hxBi
    exact ForcingKernelImage.mapsTo_unique_reuse hM hpre hp hq hqp hf
      (hDomain x hx) (hDomain y hy) (hDomain z hz) hxX hAppY hAppZ
  · intro y hy q hq _hqp hyYi r hr hrq
    have hAt := ((ForcingSliceGeometry.mem_Ypart hM env rho G F mul top O f s A X Y i hpre hY (hDomain y hy) hYP hq).mp hyYi).2
    have hImage := (ForcingSliceGeometry.occurrence_iff_B hM env rho G F mul top f s A X Y ci hpre hX hCi hB).mp hAt.2.1
    obtain ⟨t,htP,htr,x,hx,hxBi,_hyY,hApp⟩ := hImage r hr hrq
    have htq := hpre.2 t r q htP hr hq htr hrq
    have hyYi' := ForcingAtomicBasic.mem_mono hM hpre htP htq hyYi
    have hxSi := (ForcingSliceGeometry.mem_Spart hM hpre hSP htP).mpr
      ⟨hxBi,fun b hb hbt => ⟨b,hb,hpre.1 b hb,y,hDomain y hy,
        ForcingAtomicBasic.mem_mono hM hpre hb hbt hxBi,ForcingAtomicBasic.mem_mono hM hpre hb hbt hyYi',
        ForcingFormula.mono hM hpre (Source.SetLanguage.edge 0 1 2) (args3 (env f) x y) htP hb hbt hApp⟩⟩
    exact ⟨t,htP,htr,x,(ForcingRelationGraphApplication.hs_actionAt env rho _ _ _ _).mpr
      ((domain_semantics env rho G F x).mp hx),hxSi,
      (part_semantics hM env rho G F mul f Si Yi hpre htP).mpr ⟨hxSi,hyYi',hApp⟩⟩

/-- Source Spart_subset. No assertion that the source pieces cover X. -/
theorem Spart_subset (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (G F mul f s A X ci Bi Yi Si : Fin k)
    {nu p : M.Carrier .set}
    (hpre : ForcingAtomicBasic.PreorderOn (orderFormula (rho 0) mul) env (env (rho 6)))
    (hX : HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) (env X))
    (hNu : Predicate (domain rho G F) env nu)
    (hB : ForcingSliceSelection.Selected (orderFormula (rho 0) mul) (BPredicate rho G F mul s A X ci)
      env (env (rho 6)) (env X) (env Bi))
    (hSP : ForcingSeparation.Separated (orderFormula (rho 0) mul) (domain rho G F) env
      (args3 (env f) (env Bi) (env Yi)) (env (rho 6)) (env Bi) (env Si) ForcingSliceGeometry.preimageFormula)
    (hp : (Project.FirstOrderSemantics.reduct M).mem p (env (rho 6)))
    (hMem : Forces false (orderFormula (rho 0) mul) env (env (rho 6)) nu (env Si) p) :
    Forces false (orderFormula (rho 0) mul) env (env (rho 6)) nu (env X) p :=
  B_subset hM env rho G F mul s A X ci Bi hpre hX hNu hB hp
    ((ForcingSliceGeometry.mem_Spart hM hpre hSP hp).mp hMem).1

/-- Pinned Spart_disjoint. Both actual preimage witnesses are refined to
ONE internal condition; f is used only on X, then Ypart uniqueness applies. -/
theorem Spart_disjoint (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k)
    (G F mul top O f s A X Y i j ci Bi Bj Yi Yj Si Sj p q : Fin k)
    {x : M.Carrier .set}
    (hpre : ForcingAtomicBasic.PreorderOn (orderFormula (rho 0) mul) env (env (rho 6)))
    (hO : ForcingRawRank.Ordinal (env O))
    (hX : HS actionFormula (fun a => env (rho a)) (env G) (env (rho 6)) (env F) (env X))
    (hY : HS actionFormula (fun a => env (rho a)) (env G) (env (rho 6)) (env F) (env Y))
    (hx : Predicate (domain rho G F) env x)
    (hB : ForcingSliceSelection.Selected (orderFormula (rho 0) mul) (BPredicate rho G F mul s A X ci)
      env (env (rho 6)) (env X) (env Bi))
    (hYPi : ForcingSliceSelection.Selected (orderFormula (rho 0) mul) (ForcingSliceGeometry.YPredicate rho G F mul top O f s A X Y i)
      env (env (rho 6)) (env Y) (env Yi))
    (hYPj : ForcingSliceSelection.Selected (orderFormula (rho 0) mul) (ForcingSliceGeometry.YPredicate rho G F mul top O f s A X Y j)
      env (env (rho 6)) (env Y) (env Yj))
    (hSPi : ForcingSeparation.Separated (orderFormula (rho 0) mul) (domain rho G F) env
      (args3 (env f) (env Bi) (env Yi)) (env (rho 6)) (env Bi) (env Si) ForcingSliceGeometry.preimageFormula)
    (hSPj : ForcingSeparation.Separated (orderFormula (rho 0) mul) (domain rho G F) env
      (args3 (env f) (env Bj) (env Yj)) (env (rho 6)) (env Bj) (env Sj) ForcingSliceGeometry.preimageFormula)
    (hp : (Project.FirstOrderSemantics.reduct M).mem (env p) (env (rho 6)))
    (hf : Force (orderFormula (rho 0) mul) (domain rho G F) env (args3 (env f) (env X) (env Y))
      (env (rho 6)) (env p) (Source.SetLanguage.mapsTo 0 1 2))
    (hq : (Project.FirstOrderSemantics.reduct M).mem (env q) (env (rho 6)))
    (hqp : MapRel (orderFormula (rho 0) mul) env (env q) (env p))
    (hi : Forces false (orderFormula (rho 0) mul) env (env (rho 6)) x (env Si) (env q))
    (hj : Forces false (orderFormula (rho 0) mul) env (env (rho 6)) x (env Sj) (env q)) : env i = env j := by
  obtain ⟨r,hr,hrq,y,hy,hxBi,hyYi,hAppY⟩ := ((ForcingSliceGeometry.mem_Spart hM hpre hSPi hq).mp hi).2
    (env q) hq (hpre.1 (env q) hq)
  obtain ⟨t,ht,htr,z,hz,_hxBj,hzYj,hAppZ⟩ := ((ForcingSliceGeometry.mem_Spart hM hpre hSPj hq).mp hj).2 r hr hrq
  have htq := hpre.2 t r (env q) ht hr hq htr hrq
  have htp := hpre.2 t (env q) (env p) ht hq hp htq hqp
  have hxX := B_subset hM env rho G F mul s A X ci Bi hpre hX hx hB ht
    (ForcingAtomicBasic.mem_mono hM hpre ht htr hxBi)
  have heq := ForcingKernelImage.mapsTo_unique_reuse hM hpre hp ht htp hf hx hy hz hxX
    (ForcingFormula.mono hM hpre (Source.SetLanguage.edge 0 1 2) (args3 (env f) x y) hr ht htr hAppY) hAppZ
  have hzYi := (ForcingAtomicLaws.mem_congr_left hM hpre heq).mp
    (ForcingAtomicBasic.mem_mono hM hpre ht htr hyYi)
  exact ForcingSliceGeometry.Ypart_disjoint hM env rho G F mul top O f s A X Y i j
    hpre hO hY hz hYPi hYPj ht hzYi hzYj

def SurjectionResult {k : Nat} (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k)
    (G F S mul top D E p : Fin k) (Q : Formula (k+3)) : Prop :=
  ∃ graph, ForcingRelationGraph.Graph (orderFormula (rho 0) mul) Q env (rho 6) top D E graph ∧
    HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) graph ∧
    Supported (fun j => env (rho j)) (env S) graph ∧
    Force (orderFormula (rho 0) mul) (domain rho G F) env (args3 graph (env D) (env E))
      (env (rho 6)) (env p) (Source.SetLanguage.surjection 0 1 2)

def surjectionResult {k : Nat} (rho : Fin 7 → Fin k) (G F S mul top D E p : Fin k)
    (Q : Formula (k+3)) : Formula k :=
  .ex ((ForcingRelationGraph.graph (orderFormula (rho 0) mul) Q Fin.castSucc (rho 6) top D E (Fin.last k)).conj
    ((ForcingHS.hs actionFormula (fun j => (rho j).castSucc) G.castSucc (rho 6).castSucc F.castSucc (Fin.last k)).conj
      ((ForcingEquivariantMix.fixedAll (fun j => (rho j).castSucc) S.castSucc (Fin.last k)).conj
        (ForcingFormula.formula (orderFormula (rho 0) mul) (domain rho G F) Fin.castSucc
          (args3 (Fin.last k) D.castSucc E.castSucc) (rho 6).castSucc p.castSucc (Source.SetLanguage.surjection 0 1 2)))))

theorem surjectionResult_semantics {k : Nat} (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k)
    (G F S mul top D E p : Fin k) (Q : Formula (k+3)) :
    Formula.Realize (Project.FirstOrderSemantics.reduct M).mem env (surjectionResult rho G F S mul top D E p Q) ↔
      SurjectionResult env rho G F S mul top D E p Q := by
  simp only [surjectionResult,SurjectionResult,Formula.Realize,ForcingRelationGraph.graph_semantics,
    ForcingHS.hs_semantics,ForcingEquivariantMix.fixedAll_semantics,ForcingFormula.formula_semantics,
    Fin.lastCases_last,Fin.lastCases_castSucc,args3_map]
  rfl

/-- The piece equations below are the actual constructor outputs already
proved in ForcingSliceGeometry.family_kernel_certificate, not new correctness
oracles. This consumer constructs the graph and its full function laws. -/
def sliceSentence {k : Nat} (rho : Fin 7 → Fin k)
    (I K B w G F S mul top s A X O checkedO i ci Bi Cart p : Fin k) : Project.Sentence where
  formula := Project.Formula.forallClosure k
    ([ProjectSyntax.encode id (ForcingProductFamily.presentation (rho 0) I K B w (rho 1) (rho 2) (rho 3) (rho 4) (rho 5) (rho 6)),
      ProjectSyntax.encode id (ForcingLabelPermutations.carrier I G),
      ProjectSyntax.encode id (ForcingNormalFilter.normal I G F),
      ProjectSyntax.encode id (ForcingConjugationGraph.subgroup I G S),
      .mem (.bound S) (.bound F),
      ProjectSyntax.encode id (ForcingWithTopCarrier.empty top),
      ProjectSyntax.encode id (ForcingAtomicBasic.preorder (orderFormula (rho 0) mul) id (rho 6)),
      ProjectSyntax.encode id (ForcingHS.hs actionFormula rho G (rho 6) F A),
      ProjectSyntax.encode id (ForcingHS.hs actionFormula rho G (rho 6) F X),
      ProjectSyntax.encode id (ForcingHS.hs actionFormula rho G (rho 6) F Bi),
      ProjectSyntax.encode id (ForcingEquivariantMix.fixedAll rho S s),
      ProjectSyntax.encode id (ForcingEquivariantMix.fixedAll rho S A),
      ProjectSyntax.encode id (ForcingEquivariantMix.fixedAll rho S X),
      ProjectSyntax.encode id (ForcingEquivariantMix.fixedAll rho S Bi),
      ProjectSyntax.encode id (ForcingCheckName.checkName top O checkedO),
      .mem (.bound i) (.bound O),
      ProjectSyntax.encode id (ForcingCheckName.checkName top i ci),
      ProjectSyntax.encode id (ForcingSliceSelection.selected (orderFormula (rho 0) mul) (BPredicate rho G F mul s A X ci) id (rho 6) X Bi),
      ProjectSyntax.encode id (ForcingRelationGraph.graph (orderFormula (rho 0) mul) ForcingCompletionGraph.trueRelation id (rho 6) top A checkedO Cart),
      .mem (.bound p) (.bound (rho 6)),
      ProjectSyntax.encode id (ForcingFormula.formula (orderFormula (rho 0) mul) (domain rho G F) id
        (args3 s Cart X) (rho 6) p (Source.SetLanguage.mapsTo 0 1 2))].foldr Definitional.Formula.imp
      (ProjectSyntax.encode id (surjectionResult rho G F S mul top A Bi p (sliceRelation rho G F mul s A X ci))))
  freeClosed := by simp -implicitDefEqProofs [List.foldr,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed]

theorem slice_models {k : Nat} (rho : Fin 7 → Fin k)
    (I K B w G F S mul top s A X O checkedO i ci Bi Cart p : Fin k) (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (sliceSentence rho I K B w G F S mul top s A X O checkedO i ci Bi Cart p)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM),SetTheory.Structure.satisfiesSentence_iff]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro env
  simp only [List.foldr,Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ForcingProductFamily.presentation_semantics,
    ForcingLabelPermutations.carrier_semantics,ForcingNormalFilter.normal_semantics,ForcingConjugationGraph.subgroup_semantics,
    ForcingWithTopCarrier.empty_semantics,ForcingAtomicBasic.preorder_semantics,ForcingHS.hs_semantics,
    ForcingEquivariantMix.fixedAll_semantics,ForcingCheckName.checkName_semantics,ForcingSliceSelection.selected_semantics,
    ForcingRelationGraph.graph_semantics,ForcingFormula.formula_semantics,surjectionResult_semantics,id_eq,args3_map]
  exact sliceGraph_surjection hM env rho I K B w G F S mul top s A X O checkedO i ci Bi Cart p

theorem slice_kernel_certificate {k : Nat} (rho : Fin 7 → Fin k)
    (I K B w G F S mul top s A X O checkedO i ci Bi Cart p : Fin k) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (sliceSentence rho I K B w G F S mul top s A X O checkedO i ci Bi Cart p)) :=
  ModelTransfer.derives (fun _ hM => slice_models rho I K B w G F S mul top s A X O checkedO i ci Bi Cart p hM)

def partSentence {k : Nat} (rho : Fin 7 → Fin k)
    (I K B w G F S mul top O f s A X Y i ci Bi Yi Si p : Fin k) : Project.Sentence where
  formula := Project.Formula.forallClosure k
    ([ProjectSyntax.encode id (ForcingProductFamily.presentation (rho 0) I K B w (rho 1) (rho 2) (rho 3) (rho 4) (rho 5) (rho 6)),
      ProjectSyntax.encode id (ForcingLabelPermutations.carrier I G),
      ProjectSyntax.encode id (ForcingNormalFilter.normal I G F),
      ProjectSyntax.encode id (ForcingConjugationGraph.subgroup I G S),
      .mem (.bound S) (.bound F),
      ProjectSyntax.encode id (ForcingWithTopCarrier.empty top),
      ProjectSyntax.encode id (ForcingAtomicBasic.preorder (orderFormula (rho 0) mul) id (rho 6)),
      ProjectSyntax.encode id (ForcingHS.hs actionFormula rho G (rho 6) F X),
      ProjectSyntax.encode id (ForcingHS.hs actionFormula rho G (rho 6) F Y),
      ProjectSyntax.encode id (ForcingHS.hs actionFormula rho G (rho 6) F Yi),
      ProjectSyntax.encode id (ForcingHS.hs actionFormula rho G (rho 6) F Si),
      ProjectSyntax.encode id (ForcingEquivariantMix.fixedAll rho S f),
      ProjectSyntax.encode id (ForcingEquivariantMix.fixedAll rho S Yi),
      ProjectSyntax.encode id (ForcingEquivariantMix.fixedAll rho S Si),
      ProjectSyntax.encode id (ForcingCheckName.checkName top i ci),
      ProjectSyntax.encode id (ForcingSliceSelection.selected (orderFormula (rho 0) mul) (BPredicate rho G F mul s A X ci) id (rho 6) X Bi),
      ProjectSyntax.encode id (ForcingSliceSelection.selected (orderFormula (rho 0) mul) (ForcingSliceGeometry.YPredicate rho G F mul top O f s A X Y i) id (rho 6) Y Yi),
      ProjectSyntax.encode id (ForcingSeparation.separated (orderFormula (rho 0) mul) (domain rho G F) id
        (args3 f Bi Yi) (rho 6) Bi Si ForcingSliceGeometry.preimageFormula),
      .mem (.bound p) (.bound (rho 6)),
      ProjectSyntax.encode id (ForcingFormula.formula (orderFormula (rho 0) mul) (domain rho G F) id
        (args3 f X Y) (rho 6) p (Source.SetLanguage.mapsTo 0 1 2))].foldr Definitional.Formula.imp
      (ProjectSyntax.encode id (surjectionResult rho G F S mul top Si Yi p (partRelation rho G F mul f Si Yi))))
  freeClosed := by simp -implicitDefEqProofs [List.foldr,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed]

theorem part_models {k : Nat} (rho : Fin 7 → Fin k)
    (I K B w G F S mul top O f s A X Y i ci Bi Yi Si p : Fin k) (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (partSentence rho I K B w G F S mul top O f s A X Y i ci Bi Yi Si p)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM),SetTheory.Structure.satisfiesSentence_iff]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro env
  simp only [List.foldr,Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ForcingProductFamily.presentation_semantics,
    ForcingLabelPermutations.carrier_semantics,ForcingNormalFilter.normal_semantics,ForcingConjugationGraph.subgroup_semantics,
    ForcingWithTopCarrier.empty_semantics,ForcingAtomicBasic.preorder_semantics,ForcingHS.hs_semantics,
    ForcingEquivariantMix.fixedAll_semantics,ForcingCheckName.checkName_semantics,ForcingSliceSelection.selected_semantics,
    ForcingSeparation.separated_semantics,ForcingFormula.formula_semantics,surjectionResult_semantics,id_eq,args3_map]
  exact partGraph_surjection hM env rho I K B w G F S mul top O f s A X Y i ci Bi Yi Si p

theorem part_kernel_certificate {k : Nat} (rho : Fin 7 → Fin k)
    (I K B w G F S mul top O f s A X Y i ci Bi Yi Si p : Fin k) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (partSentence rho I K B w G F S mul top O f s A X Y i ci Bi Yi Si p)) :=
  ModelTransfer.derives (fun _ hM => part_models rho I K B w G F S mul top O f s A X Y i ci Bi Yi Si p hM)


/-- Full native object sentence for the source pairwise-disjointness consumer. -/
def disjointSentence {k : Nat} (rho : Fin 7 → Fin k) (G F mul top O f s A X Y i j ci Bi Bj Yi Yj Si Sj p q x : Fin k) : Project.Sentence where
  formula := Project.Formula.forallClosure k
    ([ProjectSyntax.encode id (ForcingAtomicBasic.preorder (orderFormula (rho 0) mul) id (rho 6)),
      ProjectSyntax.encode id (OrdinalSyntax.ordinal O),
      ProjectSyntax.encode id (ForcingHS.hs actionFormula rho G (rho 6) F X),
      ProjectSyntax.encode id (ForcingHS.hs actionFormula rho G (rho 6) F Y),
      ProjectSyntax.encode id (MinimalPredicates.pred (domain rho G F) id x),
      ProjectSyntax.encode id (ForcingSliceSelection.selected (orderFormula (rho 0) mul) (BPredicate rho G F mul s A X ci) id (rho 6) X Bi),
      ProjectSyntax.encode id (ForcingSliceSelection.selected (orderFormula (rho 0) mul) (ForcingSliceGeometry.YPredicate rho G F mul top O f s A X Y i) id (rho 6) Y Yi),
      ProjectSyntax.encode id (ForcingSliceSelection.selected (orderFormula (rho 0) mul) (ForcingSliceGeometry.YPredicate rho G F mul top O f s A X Y j) id (rho 6) Y Yj),
      ProjectSyntax.encode id (ForcingSeparation.separated (orderFormula (rho 0) mul) (domain rho G F) id (args3 f Bi Yi) (rho 6) Bi Si ForcingSliceGeometry.preimageFormula),
      ProjectSyntax.encode id (ForcingSeparation.separated (orderFormula (rho 0) mul) (domain rho G F) id (args3 f Bj Yj) (rho 6) Bj Sj ForcingSliceGeometry.preimageFormula),
      .mem (.bound p) (.bound (rho 6)),
      ProjectSyntax.encode id (ForcingFormula.formula (orderFormula (rho 0) mul) (domain rho G F) id (args3 f X Y) (rho 6) p (Source.SetLanguage.mapsTo 0 1 2)),
      .mem (.bound q) (.bound (rho 6)),
      ProjectSyntax.encode id (ReplacementPredicates.rel (orderFormula (rho 0) mul) id q p),
      ProjectSyntax.encode id (ForcingAtomicRelations.forces false (orderFormula (rho 0) mul) id (rho 6) x Si q),
      ProjectSyntax.encode id (ForcingAtomicRelations.forces false (orderFormula (rho 0) mul) id (rho 6) x Sj q)].foldr Definitional.Formula.imp
      (ProjectSyntax.encode id (Formula.equal i j)))
  freeClosed := by simp -implicitDefEqProofs [List.foldr,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed]

theorem disjoint_models {k : Nat} (rho : Fin 7 → Fin k) (G F mul top O f s A X Y i j ci Bi Bj Yi Yj Si Sj p q x : Fin k)
    (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (disjointSentence rho G F mul top O f s A X Y i j ci Bi Bj Yi Yj Si Sj p q x)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM),SetTheory.Structure.satisfiesSentence_iff]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro env
  simp only [List.foldr,Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ForcingAtomicBasic.preorder_semantics,
    ForcingRawRank.ordinal_semantics,ForcingHS.hs_semantics,ForcingClassEvaluation.predicate_semantics,
    ForcingSliceSelection.selected_semantics,ForcingSeparation.separated_semantics,
    ForcingFormula.formula_semantics,ForcingMapConditions.rel_semantics,ForcingAtomicRelations.forces_semantics,id_eq,args3_map]
  exact Spart_disjoint hM env rho G F mul top O f s A X Y i j ci Bi Bj Yi Yj Si Sj p q (x := env x)

theorem disjoint_kernel_certificate {k : Nat} (rho : Fin 7 → Fin k) (G F mul top O f s A X Y i j ci Bi Bj Yi Yj Si Sj p q x : Fin k) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (disjointSentence rho G F mul top O f s A X Y i j ci Bi Bj Yi Yj Si Sj p q x)) :=
  ModelTransfer.derives (fun _ hM => disjoint_models rho G F mul top O f s A X Y i j ci Bi Bj Yi Yj Si Sj p q x hM)

end PPAC.Migration.ForcingSliceGraphs
