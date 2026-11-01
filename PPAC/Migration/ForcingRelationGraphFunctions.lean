/- Fixed TailGraphs.BinaryRelation.graph_functionOn/mapsTo/surjection and
UniformNames.BinaryRelation.graph_injection. Preserve the full source function
formula, including exclusion of non-pairs and entries outside its domain. -/
import PPAC.Migration.ForcingRelationGraphApplication

namespace PPAC.Migration.ForcingRelationGraphFunctions
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open Source (Formula)
open Source.SetLanguage (args2 args3)
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open ForcingAtomicRelations (Forces)
open ForcingMapConditions (MapRel)
open ForcingFormula (Force)
open ForcingHS (HS)
open ForcingProductFamily (Presentation actionFormula)
open ForcingProductSymmetry (orderFormula)
open ForcingPairUnion (domain domain_semantics)
open ForcingRelationGraphForcing (Holds Monotone Congruent Regular)
open ForcingRelationGraphApplication (actionAt hs_actionAt app_graph)
attribute [local implicit_reducible] SetTheory.signature Definitional.Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 16384
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def Total {n : Nat} (R A : Formula (n+2)) (Q : Formula (n+3))
    (env : Fin n → M.Carrier .set) (P G F X Y p : M.Carrier .set) : Prop :=
  ∀ x, HS A env G P F x → ∀ q, (Definitional.Project.FirstOrderSemantics.reduct M).mem q P →
    MapRel R env q p → Forces false R env P x X q → ∀ r,
    (Definitional.Project.FirstOrderSemantics.reduct M).mem r P → MapRel R env r q →
    ∃ s, (Definitional.Project.FirstOrderSemantics.reduct M).mem s P ∧ MapRel R env s r ∧
      ∃ y, HS A env G P F y ∧ Forces false R env P y Y s ∧ Holds Q env s x y

def One {n : Nat} (R A : Formula (n+2)) (Q : Formula (n+3))
    (env : Fin n → M.Carrier .set) (P G F p : M.Carrier .set) : Prop :=
  ∀ q, (Definitional.Project.FirstOrderSemantics.reduct M).mem q P → MapRel R env q p →
    ∀ x y z, HS A env G P F x → HS A env G P F y → HS A env G P F z →
      Holds Q env q x y → Holds Q env q x z → Forces true R env P y z q

def Onto {n : Nat} (R A : Formula (n+2)) (Q : Formula (n+3))
    (env : Fin n → M.Carrier .set) (P G F X Y p : M.Carrier .set) : Prop :=
  ∀ y, HS A env G P F y → ∀ q, (Definitional.Project.FirstOrderSemantics.reduct M).mem q P →
    MapRel R env q p → Forces false R env P y Y q → ∀ r,
    (Definitional.Project.FirstOrderSemantics.reduct M).mem r P → MapRel R env r q →
    ∃ s, (Definitional.Project.FirstOrderSemantics.reduct M).mem s P ∧ MapRel R env s r ∧
      ∃ x, HS A env G P F x ∧ Forces false R env P x X s ∧ Holds Q env s x y

def Injective {n : Nat} (R A : Formula (n+2)) (Q : Formula (n+3))
    (env : Fin n → M.Carrier .set) (P G F p : M.Carrier .set) : Prop :=
  ∀ q, (Definitional.Project.FirstOrderSemantics.reduct M).mem q P → MapRel R env q p →
    ∀ x y z, HS A env G P F x → HS A env G P F y → HS A env G P F z →
      Holds Q env q x z → Holds Q env q y z → Forces true R env P x y q

theorem graph_functionOn (hM : FirstOrder.Theory.Models M nativeZF) {n m : Nat}
    (env : Fin n → M.Carrier .set) (rho : Fin 7 → Fin n) (G F mul t X Y : Fin n)
    (Q : Formula (n+3)) (v : Fin m → M.Carrier .set) (f d : Fin m) {I K B w p : M.Carrier .set}
    (hpres : Presentation (env (rho 0)) I K B w (env (rho 1)) (env (rho 2))
      (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hG : ForcingLabelPermutations.Carrier I (env G)) (hF : ForcingNormalFilter.Normal I (env G) (env F))
    (ht : ForcingWithTopCarrier.Empty (env t))
    (hpre : ForcingAtomicBasic.PreorderOn (orderFormula (rho 0) mul) env (env (rho 6)))
    (hX : HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) (env X))
    (hY : HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) (env Y))
    (hmono : Monotone (orderFormula (rho 0) mul) (actionAt rho) Q env (env (rho 6)) (env G) (env F))
    (hcongr : Congruent (orderFormula (rho 0) mul) (actionAt rho) Q env (env (rho 6)) (env G) (env F))
    (hregular : Regular (orderFormula (rho 0) mul) (actionAt rho) Q env (env (rho 6)) (env G) (env F))
    (hgraph : ForcingRelationGraph.Graph (orderFormula (rho 0) mul) Q env (rho 6) t X Y (v f))
    (hd : v d = env X)
    (htotal : Total (orderFormula (rho 0) mul) (actionAt rho) Q env (env (rho 6)) (env G) (env F) (env X) (env Y) p)
    (hone : One (orderFormula (rho 0) mul) (actionAt rho) Q env (env (rho 6)) (env G) (env F) p)
    (hp : (Definitional.Project.FirstOrderSemantics.reduct M).mem p (env (rho 6))) :
    Force (orderFormula (rho 0) mul) (domain rho G F) env v (env (rho 6)) p (Source.SetLanguage.functionOn f d) := by
  let R := orderFormula (rho 0) mul
  let H := domain rho G F
  let W := env (rho 6)
  let v0 : Fin 2 → M.Carrier .set := fun j => v (args2 f d j)
  have htW := (hpres.2.2.2.2.2 (env t)).mpr (Or.inl ht)
  have htop : ∀ r, (Definitional.Project.FirstOrderSemantics.reduct M).mem r W → MapRel R env r (env t) :=
    fun r _ => (ForcingProductSymmetry.orderFormula_semantics env (rho 0) mul r (env t)).mpr (Or.inl ht)
  rw [Source.SetLanguage.functionOn,ForcingSound.rename hM hpre _ _ _ _ hp,ForcingFormula.force_conj]
  constructor
  · apply (ForcingFormula.force_all hM hpre hp _ _).mpr
    intro nu hnu
    have hnuHS := (domain_semantics env rho G F nu).mp hnu
    apply (ForcingFormula.force_imp hM hpre hp _ _ _).mpr
    intro q hq hqp hm
    apply (ForcingFormula.force_ex R H env _ W q _).mpr
    intro r hr hrq
    obtain ⟨s,hs,hsr,x,y,b,hx,hy,hb,hMX,_,_,he⟩ :=
      ((ForcingRelationGraphForcing.mem_graph hM R (actionAt rho) Q env (rho 6) G F t X Y hpre htW htop
        ((hs_actionAt env rho _ _ _ _).mpr hX) ((hs_actionAt env rho _ _ _ _).mpr hY)
        hmono hcongr hgraph hq).mp hm) r hr hrq
    have hxHS := (hs_actionAt env rho _ _ _ _).mp hx
    have hyHS := (hs_actionAt env rho _ _ _ _).mp hy
    refine ⟨s,hs,hsr,x,(domain_semantics env rho G F x).mpr hxHS,?_⟩
    apply (ForcingFormula.force_ex R H env _ W s _).mpr
    intro u hu hus
    let vv : Fin 5 → M.Carrier .set := Fin.lastCases y (Fin.lastCases x (Fin.lastCases nu v0))
    refine ⟨u,hu,hpre.1 u hu,y,(domain_semantics env rho G F y).mpr hyHS,?_,?_⟩
    · change Forces false R env W x (v d) u
      simpa only [hd] using ForcingAtomicBasic.mem_mono hM hpre hu hus hMX
    · exact (ForcingPairFormula.forces_orderedPair hM env rho G F mul vv (2 : Fin 5) 3 4
        hpres hG hF ht hpre hnuHS hxHS hyHS hb hu).mpr (ForcingAtomicBasic.eq_mono hM hpre hu hus he)
  · apply (ForcingFormula.force_all hM hpre hp _ _).mpr
    intro x hx
    have hxHS := (domain_semantics env rho G F x).mp hx
    have hxA := (hs_actionAt env rho _ _ _ _).mpr hxHS
    apply (ForcingFormula.force_imp hM hpre hp _ _ _).mpr
    intro q hq hqp hMX
    change Forces false R env W x (v d) q at hMX
    have hMX' : Forces false R env W x (env X) q := by simpa only [hd] using hMX
    apply (ForcingFormula.force_ex R H env _ W q _).mpr
    intro r hr hrq
    obtain ⟨s,hs,hsr,y,hy,hMY,hQ⟩ := htotal x hxA q hq hqp hMX' r hr hrq
    have hyHS := (hs_actionAt env rho _ _ _ _).mp hy
    let vv : Fin 4 → M.Carrier .set := Fin.lastCases y (Fin.lastCases x v0)
    refine ⟨s,hs,hsr,y,(domain_semantics env rho G F y).mpr hyHS,?_,?_⟩
    · exact (app_graph hM env rho G F mul t X Y Q vv (0 : Fin 4) 2 3 hpres hG hF ht hpre hX hY
        hmono hcongr hregular hgraph hxHS hyHS hs).mpr
        ⟨ForcingAtomicBasic.mem_mono hM hpre hs (hpre.2 s r q hs hr hq hsr hrq) hMX',hMY,hQ⟩
    · apply (ForcingFormula.force_all hM hpre hs _ _).mpr
      intro z hz
      have hzHS := (domain_semantics env rho G F z).mp hz
      let vz : Fin 5 → M.Carrier .set := Fin.lastCases z vv
      apply (ForcingFormula.force_imp hM hpre hs _ _ _).mpr
      intro u hu hus hApp
      have huq := hpre.2 u s r hu hs hr hus hsr
      have hup := hpre.2 u q p hu hq hp (hpre.2 u r q hu hr hq huq hrq) hqp
      have hQz := ((app_graph hM env rho G F mul t X Y Q vz (0 : Fin 5) 2 4 hpres hG hF ht hpre hX hY
        hmono hcongr hregular hgraph hxHS hzHS hu).mp hApp).2.2
      exact hone u hu hup x z y hxA ((hs_actionAt env rho _ _ _ _).mpr hzHS) hy hQz
        (hmono s u x y hs hu hus hxA hy hQ)

theorem graph_mapsTo (hM : FirstOrder.Theory.Models M nativeZF) {n m : Nat}
    (env : Fin n → M.Carrier .set) (rho : Fin 7 → Fin n) (G F mul t X Y : Fin n)
    (Q : Formula (n+3)) (v : Fin m → M.Carrier .set) (f d e : Fin m) {I K B w p : M.Carrier .set}
    (hpres : Presentation (env (rho 0)) I K B w (env (rho 1)) (env (rho 2))
      (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hG : ForcingLabelPermutations.Carrier I (env G)) (hF : ForcingNormalFilter.Normal I (env G) (env F))
    (ht : ForcingWithTopCarrier.Empty (env t))
    (hpre : ForcingAtomicBasic.PreorderOn (orderFormula (rho 0) mul) env (env (rho 6)))
    (hX : HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) (env X))
    (hY : HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) (env Y))
    (hmono : Monotone (orderFormula (rho 0) mul) (actionAt rho) Q env (env (rho 6)) (env G) (env F))
    (hcongr : Congruent (orderFormula (rho 0) mul) (actionAt rho) Q env (env (rho 6)) (env G) (env F))
    (hregular : Regular (orderFormula (rho 0) mul) (actionAt rho) Q env (env (rho 6)) (env G) (env F))
    (hgraph : ForcingRelationGraph.Graph (orderFormula (rho 0) mul) Q env (rho 6) t X Y (v f))
    (hd : v d = env X) (he : v e = env Y)
    (htotal : Total (orderFormula (rho 0) mul) (actionAt rho) Q env (env (rho 6)) (env G) (env F) (env X) (env Y) p)
    (hone : One (orderFormula (rho 0) mul) (actionAt rho) Q env (env (rho 6)) (env G) (env F) p)
    (hp : (Definitional.Project.FirstOrderSemantics.reduct M).mem p (env (rho 6))) :
    Force (orderFormula (rho 0) mul) (domain rho G F) env v (env (rho 6)) p (Source.SetLanguage.mapsTo f d e) := by
  let R := orderFormula (rho 0) mul
  let H := domain rho G F
  let W := env (rho 6)
  let v0 : Fin 3 → M.Carrier .set := fun j => v (args3 f d e j)
  rw [Source.SetLanguage.mapsTo,ForcingSound.rename hM hpre _ _ _ _ hp,ForcingFormula.force_conj]
  constructor
  · exact graph_functionOn hM env rho G F mul t X Y Q v0 (0 : Fin 3) 1
      hpres hG hF ht hpre hX hY hmono hcongr hregular hgraph hd htotal hone hp
  · apply (ForcingFormula.force_all hM hpre hp _ _).mpr
    intro x hx
    apply (ForcingFormula.force_all hM hpre hp _ _).mpr
    intro y hy
    have hxHS := (domain_semantics env rho G F x).mp hx
    have hyHS := (domain_semantics env rho G F y).mp hy
    let vv : Fin 5 → M.Carrier .set := Fin.lastCases y (Fin.lastCases x v0)
    apply (ForcingFormula.force_imp hM hpre hp _ _ _).mpr
    intro q hq _ _
    apply (ForcingFormula.force_imp hM hpre hq _ _ _).mpr
    intro r hr _ hApp
    change Forces false R env W y (v e) r
    have hMY := ((app_graph hM env rho G F mul t X Y Q vv (0 : Fin 5) 3 4 hpres hG hF ht hpre hX hY
      hmono hcongr hregular hgraph hxHS hyHS hr).mp hApp).2.1
    change Forces false R env W y (env Y) r at hMY
    rw [he]
    exact hMY

theorem graph_surjection (hM : FirstOrder.Theory.Models M nativeZF) {n m : Nat}
    (env : Fin n → M.Carrier .set) (rho : Fin 7 → Fin n) (G F mul t X Y : Fin n)
    (Q : Formula (n+3)) (v : Fin m → M.Carrier .set) (f d e : Fin m) {I K B w p : M.Carrier .set}
    (hpres : Presentation (env (rho 0)) I K B w (env (rho 1)) (env (rho 2))
      (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hG : ForcingLabelPermutations.Carrier I (env G)) (hF : ForcingNormalFilter.Normal I (env G) (env F))
    (ht : ForcingWithTopCarrier.Empty (env t))
    (hpre : ForcingAtomicBasic.PreorderOn (orderFormula (rho 0) mul) env (env (rho 6)))
    (hX : HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) (env X))
    (hY : HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) (env Y))
    (hmono : Monotone (orderFormula (rho 0) mul) (actionAt rho) Q env (env (rho 6)) (env G) (env F))
    (hcongr : Congruent (orderFormula (rho 0) mul) (actionAt rho) Q env (env (rho 6)) (env G) (env F))
    (hregular : Regular (orderFormula (rho 0) mul) (actionAt rho) Q env (env (rho 6)) (env G) (env F))
    (hgraph : ForcingRelationGraph.Graph (orderFormula (rho 0) mul) Q env (rho 6) t X Y (v f))
    (hd : v d = env X) (he : v e = env Y)
    (htotal : Total (orderFormula (rho 0) mul) (actionAt rho) Q env (env (rho 6)) (env G) (env F) (env X) (env Y) p)
    (hone : One (orderFormula (rho 0) mul) (actionAt rho) Q env (env (rho 6)) (env G) (env F) p)
    (honto : Onto (orderFormula (rho 0) mul) (actionAt rho) Q env (env (rho 6)) (env G) (env F) (env X) (env Y) p)
    (hp : (Definitional.Project.FirstOrderSemantics.reduct M).mem p (env (rho 6))) :
    Force (orderFormula (rho 0) mul) (domain rho G F) env v (env (rho 6)) p (Source.SetLanguage.surjection f d e) := by
  let R := orderFormula (rho 0) mul
  let H := domain rho G F
  let W := env (rho 6)
  let v0 : Fin 3 → M.Carrier .set := fun j => v (args3 f d e j)
  rw [Source.SetLanguage.surjection,ForcingSound.rename hM hpre _ _ _ _ hp,ForcingFormula.force_conj]
  constructor
  · exact graph_mapsTo hM env rho G F mul t X Y Q v0 (0 : Fin 3) 1 2
      hpres hG hF ht hpre hX hY hmono hcongr hregular hgraph hd he htotal hone hp
  · apply (ForcingFormula.force_all hM hpre hp _ _).mpr
    intro y hy
    have hyHS := (domain_semantics env rho G F y).mp hy
    apply (ForcingFormula.force_imp hM hpre hp _ _ _).mpr
    intro q hq hqp hMY
    change Forces false R env W y (v e) q at hMY
    have hMY' : Forces false R env W y (env Y) q := by simpa only [he] using hMY
    apply (ForcingFormula.force_ex R H env _ W q _).mpr
    intro r hr hrq
    obtain ⟨s,hs,hsr,x,hx,hMX,hQ⟩ := honto y ((hs_actionAt env rho _ _ _ _).mpr hyHS) q hq hqp hMY' r hr hrq
    have hxHS := (hs_actionAt env rho _ _ _ _).mp hx
    let vv : Fin 5 → M.Carrier .set := Fin.lastCases x (Fin.lastCases y v0)
    refine ⟨s,hs,hsr,x,(domain_semantics env rho G F x).mpr hxHS,?_,?_⟩
    · change Forces false R env W x (v d) s
      simpa only [hd] using hMX
    · exact (app_graph hM env rho G F mul t X Y Q vv (0 : Fin 5) 4 3 hpres hG hF ht hpre hX hY
        hmono hcongr hregular hgraph hxHS hyHS hs).mpr
        ⟨hMX,ForcingAtomicBasic.mem_mono hM hpre hs (hpre.2 s r q hs hr hq hsr hrq) hMY',hQ⟩

theorem graph_injection (hM : FirstOrder.Theory.Models M nativeZF) {n m : Nat}
    (env : Fin n → M.Carrier .set) (rho : Fin 7 → Fin n) (G F mul t X Y : Fin n)
    (Q : Formula (n+3)) (v : Fin m → M.Carrier .set) (f d e : Fin m) {I K B w p : M.Carrier .set}
    (hpres : Presentation (env (rho 0)) I K B w (env (rho 1)) (env (rho 2))
      (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hG : ForcingLabelPermutations.Carrier I (env G)) (hF : ForcingNormalFilter.Normal I (env G) (env F))
    (ht : ForcingWithTopCarrier.Empty (env t))
    (hpre : ForcingAtomicBasic.PreorderOn (orderFormula (rho 0) mul) env (env (rho 6)))
    (hX : HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) (env X))
    (hY : HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) (env Y))
    (hmono : Monotone (orderFormula (rho 0) mul) (actionAt rho) Q env (env (rho 6)) (env G) (env F))
    (hcongr : Congruent (orderFormula (rho 0) mul) (actionAt rho) Q env (env (rho 6)) (env G) (env F))
    (hregular : Regular (orderFormula (rho 0) mul) (actionAt rho) Q env (env (rho 6)) (env G) (env F))
    (hgraph : ForcingRelationGraph.Graph (orderFormula (rho 0) mul) Q env (rho 6) t X Y (v f))
    (hd : v d = env X) (he : v e = env Y)
    (htotal : Total (orderFormula (rho 0) mul) (actionAt rho) Q env (env (rho 6)) (env G) (env F) (env X) (env Y) p)
    (hone : One (orderFormula (rho 0) mul) (actionAt rho) Q env (env (rho 6)) (env G) (env F) p)
    (hinj : Injective (orderFormula (rho 0) mul) (actionAt rho) Q env (env (rho 6)) (env G) (env F) p)
    (hp : (Definitional.Project.FirstOrderSemantics.reduct M).mem p (env (rho 6))) :
    Force (orderFormula (rho 0) mul) (domain rho G F) env v (env (rho 6)) p (Source.SetLanguage.injection f d e) := by
  let R := orderFormula (rho 0) mul
  let H := domain rho G F
  let W := env (rho 6)
  let v0 : Fin 3 → M.Carrier .set := fun j => v (args3 f d e j)
  rw [Source.SetLanguage.injection,ForcingSound.rename hM hpre _ _ _ _ hp,ForcingFormula.force_conj]
  constructor
  · exact graph_mapsTo hM env rho G F mul t X Y Q v0 (0 : Fin 3) 1 2
      hpres hG hF ht hpre hX hY hmono hcongr hregular hgraph hd he htotal hone hp
  · apply (ForcingFormula.force_all hM hpre hp _ _).mpr
    intro x hx
    apply (ForcingFormula.force_all hM hpre hp _ _).mpr
    intro y hy
    apply (ForcingFormula.force_all hM hpre hp _ _).mpr
    intro z hz
    have hxHS := (domain_semantics env rho G F x).mp hx
    have hyHS := (domain_semantics env rho G F y).mp hy
    have hzHS := (domain_semantics env rho G F z).mp hz
    let vv : Fin 6 → M.Carrier .set := Fin.lastCases z (Fin.lastCases y (Fin.lastCases x v0))
    apply (ForcingFormula.force_imp hM hpre hp _ _ _).mpr
    intro q hq hqp _
    apply (ForcingFormula.force_imp hM hpre hq _ _ _).mpr
    intro r hr hrq _
    apply (ForcingFormula.force_imp hM hpre hr _ _ _).mpr
    intro u hu hur hApps
    have huxz := ((app_graph hM env rho G F mul t X Y Q vv (0 : Fin 6) 3 5 hpres hG hF ht hpre hX hY
      hmono hcongr hregular hgraph hxHS hzHS hu).mp hApps.1).2.2
    have huyz := ((app_graph hM env rho G F mul t X Y Q vv (0 : Fin 6) 4 5 hpres hG hF ht hpre hX hY
      hmono hcongr hregular hgraph hyHS hzHS hu).mp hApps.2).2.2
    exact hinj u hu (hpre.2 u q p hu hq hp (hpre.2 u r q hu hr hq hur hrq) hqp)
      x y z ((hs_actionAt env rho _ _ _ _).mpr hxHS) ((hs_actionAt env rho _ _ _ _).mpr hyHS)
      ((hs_actionAt env rho _ _ _ _).mpr hzHS) huxz huyz

def total {n m : Nat} (R A : Formula (n+2)) (Q : Formula (n+3))
    (base : Fin n → Fin m) (P G F X Y p : Fin m) : Formula m :=
  (Formula.all ((ForcingHS.hs A (fun j => (base j).castSucc) (G).castSucc (P).castSucc (F).castSucc (Fin.last m)).imp
    (Formula.all ((Formula.mem (Fin.last (m+1)) (P).castSucc.castSucc).imp
    ((ReplacementPredicates.rel R (fun j => (base j).castSucc.castSucc) (Fin.last (m+1)) (p).castSucc.castSucc).imp
    ((ForcingAtomicRelations.forces false R (fun j => (base j).castSucc.castSucc) (P).castSucc.castSucc (Fin.last m).castSucc (X).castSucc.castSucc (Fin.last (m+1))).imp
    (Formula.all ((Formula.mem (Fin.last (m+2)) (P).castSucc.castSucc.castSucc).imp
    ((ReplacementPredicates.rel R (fun j => (base j).castSucc.castSucc.castSucc) (Fin.last (m+2)) (Fin.last (m+1)).castSucc).imp
    (Formula.ex ((Formula.mem (Fin.last (m+3)) (P).castSucc.castSucc.castSucc.castSucc).conj
    ((ReplacementPredicates.rel R (fun j => (base j).castSucc.castSucc.castSucc.castSucc) (Fin.last (m+3)) (Fin.last (m+2)).castSucc).conj
    (Formula.ex ((ForcingHS.hs A (fun j => (base j).castSucc.castSucc.castSucc.castSucc.castSucc) (G).castSucc.castSucc.castSucc.castSucc.castSucc (P).castSucc.castSucc.castSucc.castSucc.castSucc (F).castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+4))).conj
    ((ForcingAtomicRelations.forces false R (fun j => (base j).castSucc.castSucc.castSucc.castSucc.castSucc) (P).castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+4)) (Y).castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+3)).castSucc).conj
    (ForcingRelationGraphSupport.relation Q (fun j => (base j).castSucc.castSucc.castSucc.castSucc.castSucc) (Fin.last (m+3)).castSucc (Fin.last m).castSucc.castSucc.castSucc.castSucc (Fin.last (m+4))))))))))))))))))

theorem total_semantics {n m : Nat} (v : Fin m → M.Carrier .set)
    (R A : Formula (n+2)) (Q : Formula (n+3)) (base : Fin n → Fin m) (P G F X Y p : Fin m) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem v (total R A Q base P G F X Y p) ↔
      Total R A Q (fun j => v (base j)) (v P) (v G) (v F) (v X) (v Y) (v p) := by
  simp only [total,Total,ForcingRelationGraphForcing.Holds,Formula.Realize,
    ForcingMapConditions.rel_semantics (M := M),ForcingHS.hs_semantics (M := M),
    ForcingAtomicRelations.forces_semantics (M := M),ForcingRelationGraphSupport.relation_semantics (M := M),
    Fin.lastCases_last,Fin.lastCases_castSucc]
  rfl

def one {n m : Nat} (R A : Formula (n+2)) (Q : Formula (n+3))
    (base : Fin n → Fin m) (P G F p : Fin m) : Formula m :=
  (Formula.all ((Formula.mem (Fin.last m) (P).castSucc).imp
    ((ReplacementPredicates.rel R (fun j => (base j).castSucc) (Fin.last m) (p).castSucc).imp
    (Formula.all (Formula.all (Formula.all ((ForcingHS.hs A (fun j => (base j).castSucc.castSucc.castSucc.castSucc) (G).castSucc.castSucc.castSucc.castSucc (P).castSucc.castSucc.castSucc.castSucc (F).castSucc.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc).imp
    ((ForcingHS.hs A (fun j => (base j).castSucc.castSucc.castSucc.castSucc) (G).castSucc.castSucc.castSucc.castSucc (P).castSucc.castSucc.castSucc.castSucc (F).castSucc.castSucc.castSucc.castSucc (Fin.last (m+2)).castSucc).imp
    ((ForcingHS.hs A (fun j => (base j).castSucc.castSucc.castSucc.castSucc) (G).castSucc.castSucc.castSucc.castSucc (P).castSucc.castSucc.castSucc.castSucc (F).castSucc.castSucc.castSucc.castSucc (Fin.last (m+3))).imp
    ((ForcingRelationGraphSupport.relation Q (fun j => (base j).castSucc.castSucc.castSucc.castSucc) (Fin.last m).castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc (Fin.last (m+2)).castSucc).imp
    ((ForcingRelationGraphSupport.relation Q (fun j => (base j).castSucc.castSucc.castSucc.castSucc) (Fin.last m).castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc (Fin.last (m+3))).imp
    (ForcingAtomicRelations.forces true R (fun j => (base j).castSucc.castSucc.castSucc.castSucc) (P).castSucc.castSucc.castSucc.castSucc (Fin.last (m+2)).castSucc (Fin.last (m+3)) (Fin.last m).castSucc.castSucc.castSucc))))))))))))

theorem one_semantics {n m : Nat} (v : Fin m → M.Carrier .set)
    (R A : Formula (n+2)) (Q : Formula (n+3)) (base : Fin n → Fin m) (P G F p : Fin m) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem v (one R A Q base P G F p) ↔
      One R A Q (fun j => v (base j)) (v P) (v G) (v F) (v p) := by
  simp only [one,One,ForcingRelationGraphForcing.Holds,Formula.Realize,
    ForcingMapConditions.rel_semantics (M := M),ForcingHS.hs_semantics (M := M),
    ForcingAtomicRelations.forces_semantics (M := M),ForcingRelationGraphSupport.relation_semantics (M := M),
    Fin.lastCases_last,Fin.lastCases_castSucc]
  rfl

def onto {n m : Nat} (R A : Formula (n+2)) (Q : Formula (n+3))
    (base : Fin n → Fin m) (P G F X Y p : Fin m) : Formula m :=
  (Formula.all ((ForcingHS.hs A (fun j => (base j).castSucc) (G).castSucc (P).castSucc (F).castSucc (Fin.last m)).imp
    (Formula.all ((Formula.mem (Fin.last (m+1)) (P).castSucc.castSucc).imp
    ((ReplacementPredicates.rel R (fun j => (base j).castSucc.castSucc) (Fin.last (m+1)) (p).castSucc.castSucc).imp
    ((ForcingAtomicRelations.forces false R (fun j => (base j).castSucc.castSucc) (P).castSucc.castSucc (Fin.last m).castSucc (Y).castSucc.castSucc (Fin.last (m+1))).imp
    (Formula.all ((Formula.mem (Fin.last (m+2)) (P).castSucc.castSucc.castSucc).imp
    ((ReplacementPredicates.rel R (fun j => (base j).castSucc.castSucc.castSucc) (Fin.last (m+2)) (Fin.last (m+1)).castSucc).imp
    (Formula.ex ((Formula.mem (Fin.last (m+3)) (P).castSucc.castSucc.castSucc.castSucc).conj
    ((ReplacementPredicates.rel R (fun j => (base j).castSucc.castSucc.castSucc.castSucc) (Fin.last (m+3)) (Fin.last (m+2)).castSucc).conj
    (Formula.ex ((ForcingHS.hs A (fun j => (base j).castSucc.castSucc.castSucc.castSucc.castSucc) (G).castSucc.castSucc.castSucc.castSucc.castSucc (P).castSucc.castSucc.castSucc.castSucc.castSucc (F).castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+4))).conj
    ((ForcingAtomicRelations.forces false R (fun j => (base j).castSucc.castSucc.castSucc.castSucc.castSucc) (P).castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+4)) (X).castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+3)).castSucc).conj
    (ForcingRelationGraphSupport.relation Q (fun j => (base j).castSucc.castSucc.castSucc.castSucc.castSucc) (Fin.last (m+3)).castSucc (Fin.last (m+4)) (Fin.last m).castSucc.castSucc.castSucc.castSucc))))))))))))))))

theorem onto_semantics {n m : Nat} (v : Fin m → M.Carrier .set)
    (R A : Formula (n+2)) (Q : Formula (n+3)) (base : Fin n → Fin m) (P G F X Y p : Fin m) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem v (onto R A Q base P G F X Y p) ↔
      Onto R A Q (fun j => v (base j)) (v P) (v G) (v F) (v X) (v Y) (v p) := by
  simp only [onto,Onto,ForcingRelationGraphForcing.Holds,Formula.Realize,
    ForcingMapConditions.rel_semantics (M := M),ForcingHS.hs_semantics (M := M),
    ForcingAtomicRelations.forces_semantics (M := M),ForcingRelationGraphSupport.relation_semantics (M := M),
    Fin.lastCases_last,Fin.lastCases_castSucc]
  rfl

def injective {n m : Nat} (R A : Formula (n+2)) (Q : Formula (n+3))
    (base : Fin n → Fin m) (P G F p : Fin m) : Formula m :=
  (Formula.all ((Formula.mem (Fin.last m) (P).castSucc).imp
    ((ReplacementPredicates.rel R (fun j => (base j).castSucc) (Fin.last m) (p).castSucc).imp
    (Formula.all (Formula.all (Formula.all ((ForcingHS.hs A (fun j => (base j).castSucc.castSucc.castSucc.castSucc) (G).castSucc.castSucc.castSucc.castSucc (P).castSucc.castSucc.castSucc.castSucc (F).castSucc.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc).imp
    ((ForcingHS.hs A (fun j => (base j).castSucc.castSucc.castSucc.castSucc) (G).castSucc.castSucc.castSucc.castSucc (P).castSucc.castSucc.castSucc.castSucc (F).castSucc.castSucc.castSucc.castSucc (Fin.last (m+2)).castSucc).imp
    ((ForcingHS.hs A (fun j => (base j).castSucc.castSucc.castSucc.castSucc) (G).castSucc.castSucc.castSucc.castSucc (P).castSucc.castSucc.castSucc.castSucc (F).castSucc.castSucc.castSucc.castSucc (Fin.last (m+3))).imp
    ((ForcingRelationGraphSupport.relation Q (fun j => (base j).castSucc.castSucc.castSucc.castSucc) (Fin.last m).castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc (Fin.last (m+3))).imp
    ((ForcingRelationGraphSupport.relation Q (fun j => (base j).castSucc.castSucc.castSucc.castSucc) (Fin.last m).castSucc.castSucc.castSucc (Fin.last (m+2)).castSucc (Fin.last (m+3))).imp
    (ForcingAtomicRelations.forces true R (fun j => (base j).castSucc.castSucc.castSucc.castSucc) (P).castSucc.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc (Fin.last (m+2)).castSucc (Fin.last m).castSucc.castSucc.castSucc))))))))))))

theorem injective_semantics {n m : Nat} (v : Fin m → M.Carrier .set)
    (R A : Formula (n+2)) (Q : Formula (n+3)) (base : Fin n → Fin m) (P G F p : Fin m) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem v (injective R A Q base P G F p) ↔
      Injective R A Q (fun j => v (base j)) (v P) (v G) (v F) (v p) := by
  simp only [injective,Injective,ForcingRelationGraphForcing.Holds,Formula.Realize,
    ForcingMapConditions.rel_semantics (M := M),ForcingHS.hs_semantics (M := M),
    ForcingAtomicRelations.forces_semantics (M := M),ForcingRelationGraphSupport.relation_semantics (M := M),
    Fin.lastCases_last,Fin.lastCases_castSucc]
  rfl

/-- Check the logical closure with opaque formula parameters, then specialize. -/
private theorem closed_functions_models {n : Nat}
    (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 f m o s i j : Formula n)
    (h : ∀ env : Fin n → M.Carrier .set, Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem env a0 →
      Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem env a1 →
      Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem env a2 →
      Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem env a3 →
      Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem env a4 →
      Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem env a5 →
      Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem env a6 →
      Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem env a7 →
      Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem env a8 →
      Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem env a9 →
      Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem env a10 →
      Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem env a11 →
      Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem env a12 →
      Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem env a13 →
      (Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem env f) ∧ (Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem env m) ∧ ((Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem env o) → Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem env s) ∧ ((Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem env i) → Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem env j)) :
    (Translation.sentence ((a0.imp (a1.imp (a2.imp (a3.imp (a4.imp (a5.imp (a6.imp (a7.imp (a8.imp (a9.imp (a10.imp (a11.imp (a12.imp (a13.imp (f.conj (m.conj ((o.imp s).conj (i.imp j)))))))))))))))))).close)).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  exact h

def functionsSentence {n : Nat} (Q : Formula (n+3)) (rho : Fin 7 → Fin n)
    (I K B w G F mul t X Y name p : Fin n) : Source.Sentence :=
  ((ForcingProductFamily.presentation (rho 0) I K B w (rho 1) (rho 2) (rho 3) (rho 4) (rho 5) (rho 6)).imp (
    (ForcingLabelPermutations.carrier I G).imp (
    (ForcingNormalFilter.normal I G F).imp (
    (ForcingWithTopCarrier.empty t).imp (
    (ForcingAtomicBasic.preorder (orderFormula (rho 0) mul) id (rho 6)).imp (
    (ForcingHS.hs actionFormula rho G (rho 6) F X).imp (
    (ForcingHS.hs actionFormula rho G (rho 6) F Y).imp (
    (ForcingRelationGraphForcing.monotone (orderFormula (rho 0) mul) (actionAt rho) Q id (rho 6) G F).imp (
    (ForcingRelationGraphForcing.congruent (orderFormula (rho 0) mul) (actionAt rho) Q id (rho 6) G F).imp (
    (ForcingRelationGraphForcing.regular (orderFormula (rho 0) mul) (actionAt rho) Q id (rho 6) G F).imp (
    (ForcingRelationGraph.graph (orderFormula (rho 0) mul) Q id (rho 6) t X Y name).imp (
    (total (orderFormula (rho 0) mul) (actionAt rho) Q id (rho 6) G F X Y p).imp (
    (one (orderFormula (rho 0) mul) (actionAt rho) Q id (rho 6) G F p).imp (
    (Formula.mem p (rho 6)).imp (
    (ForcingFormula.formula (orderFormula (rho 0) mul) (domain rho G F) id id (rho 6) p (Source.SetLanguage.functionOn name X)).conj (
    (ForcingFormula.formula (orderFormula (rho 0) mul) (domain rho G F) id id (rho 6) p (Source.SetLanguage.mapsTo name X Y)).conj (
    ((onto (orderFormula (rho 0) mul) (actionAt rho) Q id (rho 6) G F X Y p).imp (ForcingFormula.formula (orderFormula (rho 0) mul) (domain rho G F) id id (rho 6) p (Source.SetLanguage.surjection name X Y))).conj (
    (injective (orderFormula (rho 0) mul) (actionAt rho) Q id (rho 6) G F p).imp (ForcingFormula.formula (orderFormula (rho 0) mul) (domain rho G F) id id (rho 6) p (Source.SetLanguage.injection name X Y)))))))))))))))))))).close

theorem functions_models {n : Nat} (Q : Formula (n+3)) (rho : Fin 7 → Fin n)
    (I K B w G F mul t X Y name p : Fin n) (hM : FirstOrder.Theory.Models M nativeZF) :
    (Translation.sentence (functionsSentence Q rho I K B w G F mul t X Y name p)).TrueIn M := by

  apply closed_functions_models

  intro env hpres hG hF ht hpre hX hY hmono hcongr hregular hgraph htotal hone hp

  constructor
  · exact (ForcingFormula.formula_semantics (M := M) env (orderFormula (rho 0) mul) (domain rho G F) id id (rho 6) p (Source.SetLanguage.functionOn name X)).mpr
      (graph_functionOn hM env rho G F mul t X Y Q env name X
        ((ForcingProductFamily.presentation_semantics (M := M) env (rho 0) I K B w (rho 1) (rho 2) (rho 3) (rho 4) (rho 5) (rho 6)).mp hpres) ((ForcingLabelPermutations.carrier_semantics (M := M) env I G).mp hG) ((ForcingNormalFilter.normal_semantics (M := M) env I G F).mp hF) ((ForcingWithTopCarrier.empty_semantics (M := M) env t).mp ht) ((ForcingAtomicBasic.preorder_semantics (M := M) env (orderFormula (rho 0) mul) id (rho 6)).mp hpre) ((ForcingHS.hs_semantics (M := M) env actionFormula rho G (rho 6) F X).mp hX) ((ForcingHS.hs_semantics (M := M) env actionFormula rho G (rho 6) F Y).mp hY) ((ForcingRelationGraphForcing.monotone_semantics (M := M) env (orderFormula (rho 0) mul) (actionAt rho) Q id (rho 6) G F).mp hmono) ((ForcingRelationGraphForcing.congruent_semantics (M := M) env (orderFormula (rho 0) mul) (actionAt rho) Q id (rho 6) G F).mp hcongr) ((ForcingRelationGraphForcing.regular_semantics (M := M) env (orderFormula (rho 0) mul) (actionAt rho) Q id (rho 6) G F).mp hregular) ((ForcingRelationGraph.graph_semantics (M := M) env (orderFormula (rho 0) mul) Q id (rho 6) t X Y name).mp hgraph) rfl ((total_semantics (M := M) env (orderFormula (rho 0) mul) (actionAt rho) Q id (rho 6) G F X Y p).mp htotal) ((one_semantics (M := M) env (orderFormula (rho 0) mul) (actionAt rho) Q id (rho 6) G F p).mp hone) hp)
  · constructor
    · exact (ForcingFormula.formula_semantics (M := M) env (orderFormula (rho 0) mul) (domain rho G F) id id (rho 6) p (Source.SetLanguage.mapsTo name X Y)).mpr
        (graph_mapsTo hM env rho G F mul t X Y Q env name X Y
          ((ForcingProductFamily.presentation_semantics (M := M) env (rho 0) I K B w (rho 1) (rho 2) (rho 3) (rho 4) (rho 5) (rho 6)).mp hpres) ((ForcingLabelPermutations.carrier_semantics (M := M) env I G).mp hG) ((ForcingNormalFilter.normal_semantics (M := M) env I G F).mp hF) ((ForcingWithTopCarrier.empty_semantics (M := M) env t).mp ht) ((ForcingAtomicBasic.preorder_semantics (M := M) env (orderFormula (rho 0) mul) id (rho 6)).mp hpre) ((ForcingHS.hs_semantics (M := M) env actionFormula rho G (rho 6) F X).mp hX) ((ForcingHS.hs_semantics (M := M) env actionFormula rho G (rho 6) F Y).mp hY) ((ForcingRelationGraphForcing.monotone_semantics (M := M) env (orderFormula (rho 0) mul) (actionAt rho) Q id (rho 6) G F).mp hmono) ((ForcingRelationGraphForcing.congruent_semantics (M := M) env (orderFormula (rho 0) mul) (actionAt rho) Q id (rho 6) G F).mp hcongr) ((ForcingRelationGraphForcing.regular_semantics (M := M) env (orderFormula (rho 0) mul) (actionAt rho) Q id (rho 6) G F).mp hregular) ((ForcingRelationGraph.graph_semantics (M := M) env (orderFormula (rho 0) mul) Q id (rho 6) t X Y name).mp hgraph) rfl rfl ((total_semantics (M := M) env (orderFormula (rho 0) mul) (actionAt rho) Q id (rho 6) G F X Y p).mp htotal) ((one_semantics (M := M) env (orderFormula (rho 0) mul) (actionAt rho) Q id (rho 6) G F p).mp hone) hp)
    · constructor
      · intro hextra
        have hextra' := (onto_semantics (M := M) env (orderFormula (rho 0) mul) (actionAt rho) Q id (rho 6) G F X Y p).mp hextra
        exact (ForcingFormula.formula_semantics (M := M) env (orderFormula (rho 0) mul) (domain rho G F) id id (rho 6) p (Source.SetLanguage.surjection name X Y)).mpr
          (graph_surjection hM env rho G F mul t X Y Q env name X Y
            ((ForcingProductFamily.presentation_semantics (M := M) env (rho 0) I K B w (rho 1) (rho 2) (rho 3) (rho 4) (rho 5) (rho 6)).mp hpres) ((ForcingLabelPermutations.carrier_semantics (M := M) env I G).mp hG) ((ForcingNormalFilter.normal_semantics (M := M) env I G F).mp hF) ((ForcingWithTopCarrier.empty_semantics (M := M) env t).mp ht) ((ForcingAtomicBasic.preorder_semantics (M := M) env (orderFormula (rho 0) mul) id (rho 6)).mp hpre) ((ForcingHS.hs_semantics (M := M) env actionFormula rho G (rho 6) F X).mp hX) ((ForcingHS.hs_semantics (M := M) env actionFormula rho G (rho 6) F Y).mp hY) ((ForcingRelationGraphForcing.monotone_semantics (M := M) env (orderFormula (rho 0) mul) (actionAt rho) Q id (rho 6) G F).mp hmono) ((ForcingRelationGraphForcing.congruent_semantics (M := M) env (orderFormula (rho 0) mul) (actionAt rho) Q id (rho 6) G F).mp hcongr) ((ForcingRelationGraphForcing.regular_semantics (M := M) env (orderFormula (rho 0) mul) (actionAt rho) Q id (rho 6) G F).mp hregular) ((ForcingRelationGraph.graph_semantics (M := M) env (orderFormula (rho 0) mul) Q id (rho 6) t X Y name).mp hgraph) rfl rfl ((total_semantics (M := M) env (orderFormula (rho 0) mul) (actionAt rho) Q id (rho 6) G F X Y p).mp htotal) ((one_semantics (M := M) env (orderFormula (rho 0) mul) (actionAt rho) Q id (rho 6) G F p).mp hone) hextra' hp)
      · intro hextra

        have hextra' := (injective_semantics (M := M) env (orderFormula (rho 0) mul) (actionAt rho) Q id (rho 6) G F p).mp hextra

        exact (ForcingFormula.formula_semantics (M := M) env (orderFormula (rho 0) mul) (domain rho G F) id id (rho 6) p (Source.SetLanguage.injection name X Y)).mpr
          (graph_injection hM env rho G F mul t X Y Q env name X Y
            ((ForcingProductFamily.presentation_semantics (M := M) env (rho 0) I K B w (rho 1) (rho 2) (rho 3) (rho 4) (rho 5) (rho 6)).mp hpres) ((ForcingLabelPermutations.carrier_semantics (M := M) env I G).mp hG) ((ForcingNormalFilter.normal_semantics (M := M) env I G F).mp hF) ((ForcingWithTopCarrier.empty_semantics (M := M) env t).mp ht) ((ForcingAtomicBasic.preorder_semantics (M := M) env (orderFormula (rho 0) mul) id (rho 6)).mp hpre) ((ForcingHS.hs_semantics (M := M) env actionFormula rho G (rho 6) F X).mp hX) ((ForcingHS.hs_semantics (M := M) env actionFormula rho G (rho 6) F Y).mp hY) ((ForcingRelationGraphForcing.monotone_semantics (M := M) env (orderFormula (rho 0) mul) (actionAt rho) Q id (rho 6) G F).mp hmono) ((ForcingRelationGraphForcing.congruent_semantics (M := M) env (orderFormula (rho 0) mul) (actionAt rho) Q id (rho 6) G F).mp hcongr) ((ForcingRelationGraphForcing.regular_semantics (M := M) env (orderFormula (rho 0) mul) (actionAt rho) Q id (rho 6) G F).mp hregular) ((ForcingRelationGraph.graph_semantics (M := M) env (orderFormula (rho 0) mul) Q id (rho 6) t X Y name).mp hgraph) rfl rfl ((total_semantics (M := M) env (orderFormula (rho 0) mul) (actionAt rho) Q id (rho 6) G F X Y p).mp htotal) ((one_semantics (M := M) env (orderFormula (rho 0) mul) (actionAt rho) Q id (rho 6) G F p).mp hone) hextra' hp)

theorem functions_kernel_certificate {n : Nat} (Q : Formula (n+3)) (rho : Fin 7 → Fin n)
    (I K B w G F mul t X Y name p : Fin n) :
    FirstOrder.Derives nativeZF [] (Translation.sentence (functionsSentence Q rho I K B w G F mul t X Y name p)) :=
  ModelTransfer.derives (fun _ hM => functions_models Q rho I K B w G F mul t X Y name p hM)

end PPAC.Migration.ForcingRelationGraphFunctions
