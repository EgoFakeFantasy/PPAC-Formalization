/- Fixed OrbitNames.forces_unorderedPair/forces_orderedPair/app_iff_mem_opair.
Interpret the original pure formulas in the actual all-rank HS domain.
Reuse forcing extensionality, the formula rules and literal pair names. -/
import PPAC.Migration.ForcingOrderedPairForcing
import PPAC.Migration.ForcingBasicSetAxioms
import PPAC.Migration.ForcingSound

namespace PPAC.Migration.ForcingPairFormula
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open Source (Formula)
open Source.SetLanguage (args3)
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open ForcingAtomicRelations (Forces)
open ForcingMapConditions (MapRel)
open ForcingFormula (Force)
open ForcingHS (HS)
open ForcingProductFamily (Presentation actionFormula)
open ForcingProductSymmetry (orderFormula)
open ForcingPairUnion (domain domain_semantics)
attribute [local implicit_reducible] SetTheory.signature Definitional.Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 16384
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

theorem forces_unorderedPair (hM : FirstOrder.Theory.Models M nativeZF) {n m : Nat}
    (env : Fin n → M.Carrier .set) (rho : Fin 7 → Fin n) (G F mul : Fin n)
    (v : Fin m → M.Carrier .set) (a x y : Fin m) {t b p : M.Carrier .set}
    (hpre : ForcingAtomicBasic.PreorderOn (orderFormula (rho 0) mul) env (env (rho 6)))
    (ht : (Definitional.Project.FirstOrderSemantics.reduct M).mem t (env (rho 6)))
    (htop : ∀ r, (Definitional.Project.FirstOrderSemantics.reduct M).mem r (env (rho 6)) → MapRel (orderFormula (rho 0) mul) env r t)
    (ha : HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) (v a))
    (hb : HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) b)
    (hpair : ForcingPairName.PairName t (v x) (v y) b)
    (hp : (Definitional.Project.FirstOrderSemantics.reduct M).mem p (env (rho 6))) :
    Force (orderFormula (rho 0) mul) (domain rho G F) env v (env (rho 6)) p (Source.SetLanguage.unorderedPair a x y) ↔
      Forces true (orderFormula (rho 0) mul) env (env (rho 6)) (v a) b p := by
  let R := orderFormula (rho 0) mul
  let H := domain rho G F
  let W := env (rho 6)
  rw [Source.SetLanguage.unorderedPair,ForcingSound.rename hM hpre _ _ _ _ hp,
    ForcingFormula.force_all hM hpre hp]
  constructor
  · intro h
    apply ForcingBasicSetAxioms.eq_of_same_members hM hpre ha hb hp
    intro nu hnu q hq hqp
    have hh := h nu ((domain_semantics env rho G F nu).mpr hnu)
    rw [Source.Formula.iff,ForcingFormula.force_conj] at hh
    constructor
    · intro hm
      have hd := (ForcingFormula.force_imp hM hpre hp _ _ _).mp hh.1 q hq hqp hm
      exact (ForcingPairUnion.mem_pair hM hpair ht htop hq).mpr
        ((ForcingFormula.force_disj R H env _ W q _ _).mp hd)
    · intro hm
      apply (ForcingFormula.force_imp hM hpre hp _ _ _).mp hh.2 q hq hqp
      apply (ForcingFormula.force_disj R H env _ W q _ _).mpr
      exact (ForcingPairUnion.mem_pair hM hpair ht htop hq).mp hm
  · intro he nu _
    rw [Source.Formula.iff,ForcingFormula.force_conj]
    constructor
    · apply (ForcingFormula.force_imp hM hpre hp _ _ _).mpr
      intro q hq hqp hm
      apply (ForcingFormula.force_disj R H env _ W q _ _).mpr
      exact (ForcingPairUnion.mem_pair hM hpair ht htop hq).mp
        ((ForcingAtomicLaws.mem_congr_right hM hpre (ForcingAtomicBasic.eq_mono hM hpre hq hqp he)).mp hm)
    · apply (ForcingFormula.force_imp hM hpre hp _ _ _).mpr
      intro q hq hqp hd
      apply (ForcingAtomicLaws.mem_congr_right hM hpre (ForcingAtomicBasic.eq_mono hM hpre hq hqp he)).mpr
      exact (ForcingPairUnion.mem_pair hM hpair ht htop hq).mpr
        ((ForcingFormula.force_disj R H env _ W q _ _).mp hd)

theorem forces_orderedPair (hM : FirstOrder.Theory.Models M nativeZF) {n m : Nat}
    (env : Fin n → M.Carrier .set) (rho : Fin 7 → Fin n) (G F mul : Fin n)
    (v : Fin m → M.Carrier .set) (a x y : Fin m) {I K B w t b p : M.Carrier .set}
    (hpres : Presentation (env (rho 0)) I K B w (env (rho 1)) (env (rho 2))
      (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hG : ForcingLabelPermutations.Carrier I (env G)) (hF : ForcingNormalFilter.Normal I (env G) (env F))
    (ht : ForcingWithTopCarrier.Empty t)
    (hpre : ForcingAtomicBasic.PreorderOn (orderFormula (rho 0) mul) env (env (rho 6)))
    (ha : HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) (v a))
    (hx : HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) (v x))
    (hy : HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) (v y))
    (hpair : ForcingOrderedPairName.OrderedPairName t (v x) (v y) b)
    (hp : (Definitional.Project.FirstOrderSemantics.reduct M).mem p (env (rho 6))) :
    Force (orderFormula (rho 0) mul) (domain rho G F) env v (env (rho 6)) p (Source.SetLanguage.orderedPair a x y) ↔
      Forces true (orderFormula (rho 0) mul) env (env (rho 6)) (v a) b p := by
  let R := orderFormula (rho 0) mul
  let H := domain rho G F
  let W := env (rho 6)
  let v0 : Fin 3 → M.Carrier .set := fun j => v (args3 a x y j)
  have htW := (hpres.2.2.2.2.2 t).mpr (Or.inl ht)
  have htop : ∀ r, (Definitional.Project.FirstOrderSemantics.reduct M).mem r W → MapRel R env r t :=
    fun r _ => (ForcingProductSymmetry.orderFormula_semantics env (rho 0) mul r t).mpr (Or.inl ht)
  obtain ⟨b1,b2,hb1,hb2,hb⟩ := hpair
  have hb1HS := ForcingProductHSPair.pair_hs hM (fun j => env (rho j)) hpres hG hF ht hx hx hb1
  have hb2HS := ForcingProductHSPair.pair_hs hM (fun j => env (rho j)) hpres hG hF ht hx hy hb2
  have hbHS := ForcingProductHSPair.pair_hs hM (fun j => env (rho j)) hpres hG hF ht hb1HS hb2HS hb
  rw [Source.SetLanguage.orderedPair,ForcingSound.rename hM hpre _ _ _ _ hp,
    ForcingFormula.force_ex]
  constructor
  · intro h
    apply ForcingAtomicBasic.eq_of_dense hM hpre hp
    intro q hq hqp
    obtain ⟨r,hr,hrq,A,hA,hrest⟩ := h q hq hqp
    obtain ⟨s,hs,hsr,C,hC,hfields⟩ :=
      (ForcingFormula.force_ex R H env _ W r _).mp hrest r hr (hpre.1 r hr)
    have hAHS := (domain_semantics env rho G F A).mp hA
    have hCHS := (domain_semantics env rho G F C).mp hC
    let v2 : Fin 5 → M.Carrier .set := Fin.lastCases C (Fin.lastCases A v0)
    obtain ⟨z,hz⟩ := ForcingPairName.exists_pairName hM t A C
    have hzHS := ForcingProductHSPair.pair_hs hM (fun j => env (rho j)) hpres hG hF ht hAHS hCHS hz
    have heA := (forces_unorderedPair hM env rho G F mul v2 (3 : Fin 5) 1 1 hpre htW htop hAHS hb1HS hb1 hs).mp hfields.1
    have heC := (forces_unorderedPair hM env rho G F mul v2 (4 : Fin 5) 1 2 hpre htW htop hCHS hb2HS hb2 hs).mp hfields.2.1
    have heZ := (forces_unorderedPair hM env rho G F mul v2 (0 : Fin 5) 3 4 hpre htW htop ha hzHS hz hs).mp hfields.2.2
    exact ⟨s,hs,hpre.2 s r q hs hr hq hsr hrq,
      ForcingAtomicLaws.eq_trans hM hpre heZ
        (ForcingOrderedPairForcing.eq_pair_congr hM hpre htW htop hz hb heA heC)⟩
  · intro he q hq hqp
    refine ⟨q,hq,hpre.1 q hq,b1,(domain_semantics env rho G F b1).mpr hb1HS,?_⟩
    apply (ForcingFormula.force_ex R H env _ W q _).mpr
    intro r hr hrq
    let v2 : Fin 5 → M.Carrier .set := Fin.lastCases b2 (Fin.lastCases b1 v0)
    refine ⟨r,hr,hpre.1 r hr,b2,(domain_semantics env rho G F b2).mpr hb2HS,?_,?_,?_⟩
    · exact (forces_unorderedPair hM env rho G F mul v2 (3 : Fin 5) 1 1 hpre htW htop hb1HS hb1HS hb1 hr).mpr
        (ForcingAtomicBasic.eq_refl hM hpre b1 r hr)
    · exact (forces_unorderedPair hM env rho G F mul v2 (4 : Fin 5) 1 2 hpre htW htop hb2HS hb2HS hb2 hr).mpr
        (ForcingAtomicBasic.eq_refl hM hpre b2 r hr)
    · exact (forces_unorderedPair hM env rho G F mul v2 (0 : Fin 5) 3 4 hpre htW htop ha hbHS hb hr).mpr
        (ForcingAtomicBasic.eq_mono hM hpre hr (hpre.2 r q p hr hq hp hrq hqp) he)

theorem app_iff_mem_opair (hM : FirstOrder.Theory.Models M nativeZF) {n m : Nat}
    (env : Fin n → M.Carrier .set) (rho : Fin 7 → Fin n) (G F mul : Fin n)
    (v : Fin m → M.Carrier .set) (f x y : Fin m) {I K B w t b p : M.Carrier .set}
    (hpres : Presentation (env (rho 0)) I K B w (env (rho 1)) (env (rho 2))
      (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hG : ForcingLabelPermutations.Carrier I (env G)) (hF : ForcingNormalFilter.Normal I (env G) (env F))
    (ht : ForcingWithTopCarrier.Empty t)
    (hpre : ForcingAtomicBasic.PreorderOn (orderFormula (rho 0) mul) env (env (rho 6)))
    (hx : HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) (v x))
    (hy : HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) (v y))
    (hpair : ForcingOrderedPairName.OrderedPairName t (v x) (v y) b)
    (hp : (Definitional.Project.FirstOrderSemantics.reduct M).mem p (env (rho 6))) :
    Force (orderFormula (rho 0) mul) (domain rho G F) env v (env (rho 6)) p (Source.SetLanguage.edge f x y) ↔
      Forces false (orderFormula (rho 0) mul) env (env (rho 6)) b (v f) p := by
  let R := orderFormula (rho 0) mul
  let H := domain rho G F
  let W := env (rho 6)
  let v0 : Fin 3 → M.Carrier .set := fun j => v (args3 f x y j)
  have hbHS := ForcingOrderedPairName.orderedPair_hs hM (fun j => env (rho j)) hpres hG hF ht hx hy hpair
  rw [Source.SetLanguage.edge,ForcingSound.rename hM hpre _ _ _ _ hp,ForcingFormula.force_ex]
  constructor
  · intro h
    apply ForcingAtomicBasic.mem_of_dense hM hpre hp
    intro q hq hqp
    obtain ⟨r,hr,hrq,z,hz,hm,he⟩ := h q hq hqp
    let vz : Fin 4 → M.Carrier .set := Fin.lastCases z v0
    have hzHS := (domain_semantics env rho G F z).mp hz
    have heq := (forces_orderedPair hM env rho G F mul vz (3 : Fin 4) 1 2
      hpres hG hF ht hpre hzHS hx hy hpair hr).mp he
    exact ⟨r,hr,hrq,(ForcingAtomicLaws.mem_congr_left hM hpre heq).mp hm⟩
  · intro hm q hq hqp
    let vb : Fin 4 → M.Carrier .set := Fin.lastCases b v0
    refine ⟨q,hq,hpre.1 q hq,b,(domain_semantics env rho G F b).mpr hbHS,
      ForcingAtomicBasic.mem_mono hM hpre hq hqp hm,?_⟩
    exact (forces_orderedPair hM env rho G F mul vb (3 : Fin 4) 1 2
      hpres hG hF ht hpre hbHS hx hy hpair hq).mpr (ForcingAtomicBasic.eq_refl hM hpre b q hq)

def orderedPairSentence {n : Nat} (rho : Fin 7 → Fin n) (I K B w G F mul t a x y b p : Fin n) : Source.Sentence :=
  (((ForcingProductFamily.presentation (rho 0) I K B w (rho 1) (rho 2) (rho 3) (rho 4) (rho 5) (rho 6)).imp
    ((ForcingLabelPermutations.carrier I G).imp
    ((ForcingNormalFilter.normal I G F).imp
    ((ForcingWithTopCarrier.empty t).imp
    ((ForcingAtomicBasic.preorder (orderFormula (rho 0) mul) id (rho 6)).imp
    ((ForcingHS.hs actionFormula rho G (rho 6) F a).imp
    ((ForcingHS.hs actionFormula rho G (rho 6) F x).imp
    ((ForcingHS.hs actionFormula rho G (rho 6) F y).imp
    ((ForcingOrderedPairName.orderedPairName t x y b).imp
    ((Formula.mem p (rho 6)).imp
    ((ForcingFormula.formula (orderFormula (rho 0) mul) (domain rho G F) id id (rho 6) p (Source.SetLanguage.orderedPair a x y)).iff
      (ForcingAtomicRelations.forces true (orderFormula (rho 0) mul) id (rho 6) a b p))))))))))))).close

theorem orderedPair_models {n : Nat} (rho : Fin 7 → Fin n) (I K B w G F mul t a x y b p : Fin n)
    (hM : FirstOrder.Theory.Models M nativeZF) :
    (Translation.sentence (orderedPairSentence rho I K B w G F mul t a x y b p)).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro env hpres hG hF ht hpre ha hx hy hpair hp
  have h := forces_orderedPair hM env rho G F mul env a x y
    ((ForcingProductFamily.presentation_semantics (M := M) env (rho 0) I K B w (rho 1) (rho 2) (rho 3) (rho 4) (rho 5) (rho 6)).mp hpres)
    ((ForcingLabelPermutations.carrier_semantics (M := M) env I G).mp hG)
    ((ForcingNormalFilter.normal_semantics (M := M) env I G F).mp hF)
    ((ForcingWithTopCarrier.empty_semantics (M := M) env t).mp ht)
    ((ForcingAtomicBasic.preorder_semantics (M := M) env (orderFormula (rho 0) mul) id (rho 6)).mp hpre)
    ((ForcingHS.hs_semantics (M := M) env actionFormula rho G (rho 6) F a).mp ha)
    ((ForcingHS.hs_semantics (M := M) env actionFormula rho G (rho 6) F x).mp hx)
    ((ForcingHS.hs_semantics (M := M) env actionFormula rho G (rho 6) F y).mp hy)
    ((ForcingOrderedPairName.orderedPairName_semantics (M := M) env t x y b).mp hpair) hp
  constructor
  · intro hf
    exact (ForcingAtomicRelations.forces_semantics (M := M) env true (orderFormula (rho 0) mul) id (rho 6) a b p).mpr
      (h.mp ((ForcingFormula.formula_semantics (M := M) env (orderFormula (rho 0) mul) (domain rho G F) id id (rho 6) p (Source.SetLanguage.orderedPair a x y)).mp hf))
  · intro hm
    exact (ForcingFormula.formula_semantics (M := M) env (orderFormula (rho 0) mul) (domain rho G F) id id (rho 6) p (Source.SetLanguage.orderedPair a x y)).mpr
      (h.mpr ((ForcingAtomicRelations.forces_semantics (M := M) env true (orderFormula (rho 0) mul) id (rho 6) a b p).mp hm))

theorem orderedPair_kernel_certificate {n : Nat} (rho : Fin 7 → Fin n) (I K B w G F mul t a x y b p : Fin n) :
    FirstOrder.Derives nativeZF [] (Translation.sentence (orderedPairSentence rho I K B w G F mul t a x y b p)) :=
  ModelTransfer.derives (fun _ hM => orderedPair_models rho I K B w G F mul t a x y b p hM)

def appSentence {n : Nat} (rho : Fin 7 → Fin n) (I K B w G F mul t f x y b p : Fin n) : Source.Sentence :=
  (((ForcingProductFamily.presentation (rho 0) I K B w (rho 1) (rho 2) (rho 3) (rho 4) (rho 5) (rho 6)).imp
    ((ForcingLabelPermutations.carrier I G).imp
    ((ForcingNormalFilter.normal I G F).imp
    ((ForcingWithTopCarrier.empty t).imp
    ((ForcingAtomicBasic.preorder (orderFormula (rho 0) mul) id (rho 6)).imp
    ((ForcingHS.hs actionFormula rho G (rho 6) F x).imp
    ((ForcingHS.hs actionFormula rho G (rho 6) F y).imp
    ((ForcingOrderedPairName.orderedPairName t x y b).imp
    ((Formula.mem p (rho 6)).imp
    ((ForcingFormula.formula (orderFormula (rho 0) mul) (domain rho G F) id id (rho 6) p (Source.SetLanguage.edge f x y)).iff
      (ForcingAtomicRelations.forces false (orderFormula (rho 0) mul) id (rho 6) b f p)))))))))))).close

theorem app_models {n : Nat} (rho : Fin 7 → Fin n) (I K B w G F mul t f x y b p : Fin n)
    (hM : FirstOrder.Theory.Models M nativeZF) :
    (Translation.sentence (appSentence rho I K B w G F mul t f x y b p)).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro env hpres hG hF ht hpre hx hy hpair hp
  have h := app_iff_mem_opair hM env rho G F mul env f x y
    ((ForcingProductFamily.presentation_semantics (M := M) env (rho 0) I K B w (rho 1) (rho 2) (rho 3) (rho 4) (rho 5) (rho 6)).mp hpres)
    ((ForcingLabelPermutations.carrier_semantics (M := M) env I G).mp hG)
    ((ForcingNormalFilter.normal_semantics (M := M) env I G F).mp hF)
    ((ForcingWithTopCarrier.empty_semantics (M := M) env t).mp ht)
    ((ForcingAtomicBasic.preorder_semantics (M := M) env (orderFormula (rho 0) mul) id (rho 6)).mp hpre)
    ((ForcingHS.hs_semantics (M := M) env actionFormula rho G (rho 6) F x).mp hx)
    ((ForcingHS.hs_semantics (M := M) env actionFormula rho G (rho 6) F y).mp hy)
    ((ForcingOrderedPairName.orderedPairName_semantics (M := M) env t x y b).mp hpair) hp
  constructor
  · intro hf
    exact (ForcingAtomicRelations.forces_semantics (M := M) env false (orderFormula (rho 0) mul) id (rho 6) b f p).mpr
      (h.mp ((ForcingFormula.formula_semantics (M := M) env (orderFormula (rho 0) mul) (domain rho G F) id id (rho 6) p (Source.SetLanguage.edge f x y)).mp hf))
  · intro hm
    exact (ForcingFormula.formula_semantics (M := M) env (orderFormula (rho 0) mul) (domain rho G F) id id (rho 6) p (Source.SetLanguage.edge f x y)).mpr
      (h.mpr ((ForcingAtomicRelations.forces_semantics (M := M) env false (orderFormula (rho 0) mul) id (rho 6) b f p).mp hm))

theorem app_kernel_certificate {n : Nat} (rho : Fin 7 → Fin n) (I K B w G F mul t f x y b p : Fin n) :
    FirstOrder.Derives nativeZF [] (Translation.sentence (appSentence rho I K B w G F mul t f x y b p)) :=
  ModelTransfer.derives (fun _ hM => app_models rho I K B w G F mul t f x y b p hM)

end PPAC.Migration.ForcingPairFormula
