/- Pinned SymmetricSets.mem_pair/mem_union and forces_pairing/forces_union.
Reuse the actual atomic relations, literal names, and the accepted HS closures.
The final native certificate uses the same all-rank HS domain and actual order. -/
import PPAC.Migration.ForcingProductHSPair
import PPAC.Migration.ForcingProductHSUnion
import PPAC.Migration.ForcingProductPoset

namespace PPAC.Migration.ForcingPairUnion
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open Source (Formula)
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open ForcingMapConditions (MapRel)
open ForcingAtomicRelations (Forces)
open ForcingAtomicBasic (PreorderOn)
open ForcingFormula (Force)
open ForcingHS (HS)
open ForcingProductFamily (Presentation)
open ForcingProductSymmetry (orderFormula orderFormula_semantics)
attribute [local implicit_reducible] SetTheory.signature Definitional.Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

/-- Source SymmetricSystem.codeOrder is false outside actual condition codes. -/
def codeOrder {n : Nat} (R : Formula (n+2)) (P : Fin n) : Formula (n+2) :=
  (Formula.mem (Fin.last n).castSucc P.castSucc.castSucc).conj
    ((Formula.mem (Fin.last (n+1)) P.castSucc.castSucc).conj R)

theorem codeOrder_semantics {n : Nat} (R : Formula (n+2)) (params : Fin n → M.Carrier .set)
    (P : Fin n) (a b : M.Carrier .set) :
    MapRel (codeOrder R P) params a b ↔
      (Definitional.Project.FirstOrderSemantics.reduct M).mem a (params P) ∧
      (Definitional.Project.FirstOrderSemantics.reduct M).mem b (params P) ∧ MapRel R params a b := by
  simp only [MapRel,codeOrder,Formula.Realize,Fin.lastCases_last,Fin.lastCases_castSucc]

/-- On actual names the guarded source code order gives the same literal union.
All three condition bounds come from the existing IsName entry theorem. -/
theorem union_codeOrder {n : Nat} (R : Formula (n+2)) (params : Fin n → M.Carrier .set)
    (P : Fin n) {sigma name : M.Carrier .set} (hs : ForcingNames.IsName (params P) sigma) :
    ForcingUnionName.UnionName (codeOrder R P) params (params P) sigma name ↔
      ForcingUnionName.UnionName R params (params P) sigma name := by
  have he : ∀ z, ForcingUnionName.Entry (codeOrder R P) params (params P) sigma z ↔
      ForcingUnionName.Entry R params (params P) sigma z := by
    intro z
    constructor
    · rintro ⟨child,q,hcode,chi,p,r,hp,hr,hq,hqp,hqr⟩
      exact ⟨child,q,hcode,chi,p,r,hp,hr,hq,
        ((codeOrder_semantics R params P q p).mp hqp).2.2,
        ((codeOrder_semantics R params P q r).mp hqr).2.2⟩
    · rintro ⟨child,q,hcode,chi,p,r,hp,hr,hq,hqp,hqr⟩
      have hchi := ForcingNames.child_condition hs hp
      exact ⟨child,q,hcode,chi,p,r,hp,hr,hq,
        (codeOrder_semantics R params P q p).mpr ⟨hq,hchi.1,hqp⟩,
        (codeOrder_semantics R params P q r).mpr ⟨hq,(ForcingNames.child_condition hchi.2 hr).1,hqr⟩⟩
  unfold ForcingUnionName.UnionName
  exact forall_congr' (fun z => iff_congr Iff.rfl (he z))

theorem mem_pair (hM : FirstOrder.Theory.Models M nativeZF) {n : Nat}
    {R : Formula (n+2)} {params : Fin n → M.Carrier .set}
    {P t sigma tau name nu p : M.Carrier .set}
    (hn : ForcingPairName.PairName t sigma tau name)
    (ht : (Definitional.Project.FirstOrderSemantics.reduct M).mem t P)
    (htop : ∀ r, (Definitional.Project.FirstOrderSemantics.reduct M).mem r P → MapRel R params r t)
    (hp : (Definitional.Project.FirstOrderSemantics.reduct M).mem p P) :
    Forces false R params P nu name p ↔
      ∀ q, (Definitional.Project.FirstOrderSemantics.reduct M).mem q P → MapRel R params q p →
        ∃ r, (Definitional.Project.FirstOrderSemantics.reduct M).mem r P ∧ MapRel R params r q ∧
          (Forces true R params P nu sigma r ∨ Forces true R params P nu tau r) := by
  constructor
  · intro h q hq hqp
    obtain ⟨r,eta,c,hr,hrq,_,he,_,heq⟩ := ((ForcingAtomicRelations.mem_iff hM R params P nu name p).mp h).2 q hq hqp
    rcases ((ForcingPairName.edge_pairName hM hn eta c).mp he).1 with hleft | hright
    · exact ⟨r,hr,hrq,Or.inl (hleft ▸ heq)⟩
    · exact ⟨r,hr,hrq,Or.inr (hright ▸ heq)⟩
  · intro h
    apply (ForcingAtomicRelations.mem_iff hM R params P nu name p).mpr
    refine ⟨hp,?_⟩
    intro q hq hqp
    obtain ⟨r,hr,hrq,heq | heq⟩ := h q hq hqp
    · exact ⟨r,sigma,t,hr,hrq,ht,(ForcingPairName.edge_pairName hM hn sigma t).mpr ⟨Or.inl rfl,rfl⟩,htop r hr,heq⟩
    · exact ⟨r,tau,t,hr,hrq,ht,(ForcingPairName.edge_pairName hM hn tau t).mpr ⟨Or.inr rfl,rfl⟩,htop r hr,heq⟩

theorem mem_union (hM : FirstOrder.Theory.Models M nativeZF) {k n : Nat}
    {A : Formula (k+2)} {aenv : Fin k → M.Carrier .set}
    {R : Formula (n+2)} {params : Fin n → M.Carrier .set}
    {G P F sigma name nu p : M.Carrier .set} (hpre : PreorderOn R params P)
    (hs : HS A aenv G P F sigma) (hn : ForcingUnionName.UnionName R params P sigma name)
    (hp : (Definitional.Project.FirstOrderSemantics.reduct M).mem p P) :
    Forces false R params P nu name p ↔
      ∀ q, (Definitional.Project.FirstOrderSemantics.reduct M).mem q P → MapRel R params q p →
        ∃ r, (Definitional.Project.FirstOrderSemantics.reduct M).mem r P ∧ MapRel R params r q ∧
          ∃ chi, HS A aenv G P F chi ∧ Forces false R params P chi sigma r ∧ Forces false R params P nu chi r := by
  constructor
  · intro h q hq hqp
    obtain ⟨r,tau,c,hr,hrq,hc,he,hrc,heq⟩ := ((ForcingAtomicRelations.mem_iff hM R params P nu name p).mp h).2 q hq hqp
    obtain ⟨chi,a,b,ha,hb,_,hca,hcb⟩ := (ForcingUnionName.edge_unionName hM hn tau c).mp he
    have hchi := ForcingHS.child hs ha
    have haP := (ForcingNames.child_condition (ForcingHS.isName hs) ha).1
    have hbP := (ForcingNames.child_condition (ForcingHS.isName hchi) hb).1
    exact ⟨r,hr,hrq,chi,hchi,
      ForcingAtomicBasic.mem_of_edge_eq hM hpre haP (hpre.2 r c a hr hc haP hrc hca) ha
        (ForcingAtomicBasic.eq_refl hM hpre chi r hr),
      ForcingAtomicBasic.mem_of_edge_eq hM hpre hbP (hpre.2 r c b hr hc hbP hrc hcb) hb heq⟩
  · intro h
    apply (ForcingAtomicRelations.mem_iff hM R params P nu name p).mpr
    refine ⟨hp,?_⟩
    intro q hq hqp
    obtain ⟨r,hr,hrq,chi,_,hchi,hnu⟩ := h q hq hqp
    obtain ⟨s,tau,c,hsP,hsr,hc,hTau,hsc,heq⟩ := ((ForcingAtomicRelations.mem_iff hM R params P chi sigma r).mp hchi).2 r hr (hpre.1 r hr)
    have hnTau := (ForcingAtomicLaws.mem_congr_right hM hpre heq).mp
      (ForcingAtomicBasic.mem_mono hM hpre hsP hsr hnu)
    obtain ⟨t,eta,d,ht,hts,_,hEta,htd,heq'⟩ := ((ForcingAtomicRelations.mem_iff hM R params P nu tau s).mp hnTau).2 s hsP (hpre.1 s hsP)
    exact ⟨t,eta,t,ht,hpre.2 t s q ht hsP hq hts (hpre.2 s r q hsP hr hq hsr hrq),ht,
      (ForcingUnionName.edge_unionName hM hn eta t).mpr
        ⟨tau,c,d,hTau,hEta,ht,hpre.2 t s c ht hsP hc hts hsc,htd⟩,hpre.1 t ht,heq'⟩

/-- The existing HS formula with the seven fixed product parameters embedded. -/
def domain {n : Nat} (rho : Fin 7 → Fin n) (G F : Fin n) : Formula (n+1) :=
  ForcingHS.hs ForcingProductFamily.actionFormula (fun j => (rho j).castSucc)
    G.castSucc (rho 6).castSucc F.castSucc (Fin.last n)

theorem domain_semantics {n : Nat} (env : Fin n → M.Carrier .set) (rho : Fin 7 → Fin n)
    (G F : Fin n) (sigma : M.Carrier .set) :
    ForcingClassEvaluation.Predicate (domain rho G F) env sigma ↔
      HS ForcingProductFamily.actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) sigma := by
  simpa only [ForcingClassEvaluation.Predicate,domain,Fin.lastCases_last,Fin.lastCases_castSucc] using
    ForcingHS.hs_semantics (M := M) (Fin.lastCases sigma env) ForcingProductFamily.actionFormula
      (fun j => (rho j).castSucc) G.castSucc (rho 6).castSucc F.castSucc (Fin.last n)

theorem forces_pairing (hM : FirstOrder.Theory.Models M nativeZF) {n : Nat}
    (env : Fin n → M.Carrier .set) (rho : Fin 7 → Fin n) (G F mul : Fin n)
    {I K B w p : M.Carrier .set}
    (hpresentation : Presentation (env (rho 0)) I K B w (env (rho 1)) (env (rho 2))
      (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hG : ForcingLabelPermutations.Carrier I (env G))
    (hF : ForcingNormalFilter.Normal I (env G) (env F))
    (hpre : PreorderOn (orderFormula (rho 0) mul) env (env (rho 6)))
    (hp : (Definitional.Project.FirstOrderSemantics.reduct M).mem p (env (rho 6))) :
    Force (orderFormula (rho 0) mul) (domain rho G F) env Fin.elim0 (env (rho 6)) p Source.SetLanguage.pairing := by
  let R := orderFormula (rho 0) mul
  let H := domain rho G F
  let W := env (rho 6)
  unfold Source.SetLanguage.pairing
  apply (ForcingFormula.force_all hM hpre hp _ _).mpr
  intro sigma hs
  apply (ForcingFormula.force_all hM hpre hp _ _).mpr
  intro tau hu
  apply (ForcingFormula.force_ex R H env _ W p _).mpr
  intro q hq hqp
  obtain ⟨t, ht⟩ := ForcingWithTopCarrier.exists_empty hM
  have htW := (hpresentation.2.2.2.2.2 t).mpr (Or.inl ht)
  have htop : ∀ r, (Definitional.Project.FirstOrderSemantics.reduct M).mem r W → MapRel R env r t :=
    fun r _ => (orderFormula_semantics env (rho 0) mul r t).mpr (Or.inl ht)
  obtain ⟨name, hn⟩ := ForcingPairName.exists_pairName hM t sigma tau
  have hsHS := (domain_semantics env rho G F sigma).mp hs
  have huHS := (domain_semantics env rho G F tau).mp hu
  have hname := ForcingProductHSPair.pair_hs hM (fun j => env (rho j)) hpresentation hG hF ht hsHS huHS hn
  refine ⟨q,hq,hpre.1 q hq,name,(domain_semantics env rho G F name).mpr hname,?_⟩
  change Force R H env (Fin.lastCases name (Fin.lastCases tau (Fin.lastCases sigma Fin.elim0))) W q
    (.all ((Formula.mem (3 : Fin 4) 2).iff ((Formula.equal 3 0).disj (.equal 3 1))))
  apply (ForcingFormula.force_all hM hpre hq _ _).mpr
  intro nu hnu
  rw [Source.Formula.iff,ForcingFormula.force_conj]
  constructor
  · apply (ForcingFormula.force_imp hM hpre hq _ _ _).mpr
    intro r hr _ hmem
    apply (ForcingFormula.force_disj R H env _ W r _ _).mpr
    exact (mem_pair hM hn htW htop hr).mp hmem
  · apply (ForcingFormula.force_imp hM hpre hq _ _ _).mpr
    intro r hr _ hdisj
    exact (mem_pair hM hn htW htop hr).mpr ((ForcingFormula.force_disj R H env _ W r _ _).mp hdisj)

theorem forces_union (hM : FirstOrder.Theory.Models M nativeZF) {n : Nat}
    (env : Fin n → M.Carrier .set) (rho : Fin 7 → Fin n) (G F mul : Fin n)
    {I K B w p : M.Carrier .set}
    (hpresentation : Presentation (env (rho 0)) I K B w (env (rho 1)) (env (rho 2))
      (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hG : ForcingLabelPermutations.Carrier I (env G))
    (hF : ForcingNormalFilter.Normal I (env G) (env F))
    (hpre : PreorderOn (orderFormula (rho 0) mul) env (env (rho 6)))
    (hp : (Definitional.Project.FirstOrderSemantics.reduct M).mem p (env (rho 6))) :
    Force (orderFormula (rho 0) mul) (domain rho G F) env Fin.elim0 (env (rho 6)) p Source.SetLanguage.union := by
  let R := orderFormula (rho 0) mul
  let H := domain rho G F
  let W := env (rho 6)
  unfold Source.SetLanguage.union
  apply (ForcingFormula.force_all hM hpre hp _ _).mpr
  intro sigma hs
  have hsHS := (domain_semantics env rho G F sigma).mp hs
  apply (ForcingFormula.force_ex R H env _ W p _).mpr
  intro q hq hqp
  obtain ⟨name,hnSource⟩ := ForcingUnionName.exists_unionName hM (codeOrder R (rho 6)) env W sigma
  have hn := (union_codeOrder R env (rho 6) (ForcingHS.isName hsHS)).mp hnSource
  have hname := ForcingProductHSUnion.union_hs hM env rho mul hpresentation hG hF hsHS hn
  refine ⟨q,hq,hpre.1 q hq,name,(domain_semantics env rho G F name).mpr hname,?_⟩
  apply (ForcingFormula.force_all hM hpre hq _ _).mpr
  intro nu hnu
  rw [Source.Formula.iff,ForcingFormula.force_conj]
  constructor
  · apply (ForcingFormula.force_imp hM hpre hq _ _ _).mpr
    intro r hr _ hmem
    apply (ForcingFormula.force_ex R H env _ W r _).mpr
    intro s hsP hsr
    obtain ⟨t,ht,hts,chi,hchi,hleft,hright⟩ := (mem_union hM hpre hsHS hn hr).mp hmem s hsP hsr
    exact ⟨t,ht,hts,chi,(domain_semantics env rho G F chi).mpr hchi,hleft,hright⟩
  · apply (ForcingFormula.force_imp hM hpre hq _ _ _).mpr
    intro r hr _ hex
    apply (mem_union hM hpre hsHS hn hr).mpr
    intro s hsP hsr
    obtain ⟨t,ht,hts,chi,hchi,hmem⟩ := (ForcingFormula.force_ex R H env _ W r _).mp hex s hsP hsr
    exact ⟨t,ht,hts,chi,(domain_semantics env rho G F chi).mp hchi,hmem.1,hmem.2⟩

/-- Both original source axioms, in the same actual HS interpretation.
The source algebra contract discharges PreorderOn inside the native theorem. -/
def sentence : Source.Sentence :=
  let rho : Fin 7 → Fin 16 := fun i => ⟨i.val, Nat.lt_trans i.isLt (by decide)⟩
  let R := orderFormula (0 : Fin 16) 13
  let H := domain rho 11 12
  ((ForcingDiagramPoset.leftCancelMonoid (0 : Fin 16) 13 14).imp
    ((ForcingProductFamily.presentation (0 : Fin 16) 7 8 9 10 1 2 3 4 5 6).imp
      ((ForcingLabelPermutations.carrier (7 : Fin 16) 11).imp
        ((ForcingNormalFilter.normal (7 : Fin 16) 11 12).imp
          ((Formula.mem (15 : Fin 16) 6).imp
            ((ForcingFormula.formula R H id Fin.elim0 6 15 Source.SetLanguage.pairing).conj
              (ForcingFormula.formula R H id Fin.elim0 6 15 Source.SetLanguage.union))))))).close

theorem models (hM : FirstOrder.Theory.Models M nativeZF) : (Translation.sentence sentence).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro env hm hp hG hF hc
  let rho : Fin 7 → Fin 16 := fun i => ⟨i.val, Nat.lt_trans i.isLt (by decide)⟩
  let R := orderFormula (0 : Fin 16) 13
  let H := domain rho 11 12
  have hm' := (ForcingDiagramPoset.leftCancelMonoid_semantics (M := M) env 0 13 14).mp hm
  have hp' := (ForcingProductFamily.presentation_semantics (M := M) env 0 7 8 9 10 1 2 3 4 5 6).mp hp
  have hG' := (ForcingLabelPermutations.carrier_semantics (M := M) env 7 11).mp hG
  have hF' := (ForcingNormalFilter.normal_semantics (M := M) env 7 11 12).mp hF
  have hpre := ForcingProductPoset.preorder env 0 13 6 hm' hp'.2.2.2.2.1 hp'.2.2.2.1 hp'.2.2.2.2.2
  have hzero : (fun i : Fin 0 => env (Fin.elim0 i)) = (Fin.elim0 : Fin 0 → M.Carrier .set) :=
    funext (fun i => Fin.elim0 i)
  constructor
  · apply (ForcingFormula.formula_semantics (M := M) env R H id Fin.elim0 6 15 Source.SetLanguage.pairing).mpr
    rw [hzero]
    exact forces_pairing hM env rho 11 12 13 hp' hG' hF' hpre hc
  · apply (ForcingFormula.formula_semantics (M := M) env R H id Fin.elim0 6 15 Source.SetLanguage.union).mpr
    rw [hzero]
    exact forces_union hM env rho 11 12 13 hp' hG' hF' hpre hc

theorem kernel_certificate : FirstOrder.Derives nativeZF [] (Translation.sentence sentence) :=
  ModelTransfer.derives (fun _ hM => models hM)

end PPAC.Migration.ForcingPairUnion
