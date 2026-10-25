/- Pinned SymmetricSets.mem_check/check_mem_of_mem/check_successor/forces_infinity.
The witness is the literal check-name of native internal omega. Existing
check recursion, HS closure, omega and extensionality are reused unchanged. -/
import PPAC.Migration.ForcingBasicSetAxioms
import PPAC.Migration.ForcingHSCheck
import PPAC.Migration.ForcingProductParameters

namespace PPAC.Migration.ForcingInfinity
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open Source (Formula)
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open ForcingMapConditions (MapRel)
open ForcingAtomicRelations (Forces)
open ForcingAtomicBasic (PreorderOn)
open ForcingFormula (Force)
open ForcingCheckName (Checked)
open ForcingProductFamily (Presentation actionFormula mapRel_action)
open ForcingProductSymmetry (orderFormula orderFormula_semantics)
open ForcingPairUnion (domain domain_semantics)
attribute [local implicit_reducible] SetTheory.signature Definitional.Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

theorem mem_check (hM : FirstOrder.Theory.Models M nativeZF) {n : Nat}
    {R : Formula (n+2)} {env : Fin n → M.Carrier .set} {P t x name nu p : M.Carrier .set}
    (hn : Checked t x name) (ht : (Definitional.Project.FirstOrderSemantics.reduct M).mem t P)
    (htop : ∀ r, (Definitional.Project.FirstOrderSemantics.reduct M).mem r P → MapRel R env r t)
    (hp : (Definitional.Project.FirstOrderSemantics.reduct M).mem p P) :
    Forces false R env P nu name p ↔ ∀ q,
      (Definitional.Project.FirstOrderSemantics.reduct M).mem q P → MapRel R env q p →
      ∃ r, (Definitional.Project.FirstOrderSemantics.reduct M).mem r P ∧ MapRel R env r q ∧
        ∃ y, (Definitional.Project.FirstOrderSemantics.reduct M).mem y x ∧
          ∃ child, Checked t y child ∧ Forces true R env P nu child r := by
  rw [ForcingAtomicRelations.mem_iff hM]
  constructor
  · intro h q hq hqp
    obtain ⟨r,child,c,hr,hrq,hc,he,hrc,heq⟩ := h.2 q hq hqp
    obtain ⟨y,hy,hyc,_⟩ := (ForcingCheckName.edge_checkName hM hn child c).mp he
    exact ⟨r,hr,hrq,y,hy,child,hyc,heq⟩
  · intro h
    refine ⟨hp,?_⟩
    intro q hq hqp
    obtain ⟨r,hr,hrq,y,hy,child,hyc,heq⟩ := h q hq hqp
    exact ⟨r,child,t,hr,hrq,ht,(ForcingCheckName.edge_checkName hM hn child t).mpr
      ⟨y,hy,hyc,rfl⟩,htop r hr,heq⟩

theorem check_mem_of_mem (hM : FirstOrder.Theory.Models M nativeZF) {n : Nat}
    {R : Formula (n+2)} {env : Fin n → M.Carrier .set} {P t x y nx ny p : M.Carrier .set}
    (hpre : PreorderOn R env P) (hx : Checked t x nx) (hy : Checked t y ny)
    (hyx : (Definitional.Project.FirstOrderSemantics.reduct M).mem y x)
    (ht : (Definitional.Project.FirstOrderSemantics.reduct M).mem t P)
    (htop : ∀ r, (Definitional.Project.FirstOrderSemantics.reduct M).mem r P → MapRel R env r t)
    (hp : (Definitional.Project.FirstOrderSemantics.reduct M).mem p P) : Forces false R env P ny nx p :=
  ForcingAtomicBasic.mem_of_edge_eq hM hpre ht (htop p hp)
    ((ForcingCheckName.edge_checkName hM hx ny t).mpr ⟨y,hyx,hy,rfl⟩)
    (ForcingAtomicBasic.eq_refl hM hpre ny p hp)

theorem check_successor (hM : FirstOrder.Theory.Models M nativeZF) {n : Nat}
    {R : Formula (n+2)} {env : Fin n → M.Carrier .set} {P t x succ nx ns nu p : M.Carrier .set}
    (hpre : PreorderOn R env P) (hx : Checked t x nx) (hs : Checked t succ ns)
    (hsucc : (Definitional.Project.FirstOrderSemantics.reduct M).SuccessorOf succ x)
    (ht : (Definitional.Project.FirstOrderSemantics.reduct M).mem t P)
    (htop : ∀ r, (Definitional.Project.FirstOrderSemantics.reduct M).mem r P → MapRel R env r t)
    (hp : (Definitional.Project.FirstOrderSemantics.reduct M).mem p P) :
    Forces false R env P nu ns p ↔ ∀ q,
      (Definitional.Project.FirstOrderSemantics.reduct M).mem q P → MapRel R env q p →
      ∃ r, (Definitional.Project.FirstOrderSemantics.reduct M).mem r P ∧ MapRel R env r q ∧
        (Forces false R env P nu nx r ∨ Forces true R env P nu nx r) := by
  constructor
  · intro hm q hq hqp
    obtain ⟨r,hr,hrq,y,hy,ny,hny,heq⟩ := (mem_check hM hs ht htop hp).mp hm q hq hqp
    rcases (hsucc y).mp hy with hyx | hyx
    · exact ⟨r,hr,hrq,Or.inl ((ForcingAtomicLaws.mem_congr_left hM hpre heq).mpr
        (check_mem_of_mem hM hpre hx hny hyx ht htop hr))⟩
    · have hyEq := (ModelTransfer.extensionality hM).eq_of_same_members y x hyx
      subst y
      have hnames := ForcingCheckName.unique hM hny hx
      exact ⟨r,hr,hrq,Or.inr (hnames ▸ heq)⟩
  · intro h
    apply (mem_check hM hs ht htop hp).mpr
    intro q hq hqp
    obtain ⟨r,hr,hrq,hm | heq⟩ := h q hq hqp
    · obtain ⟨s,hsc,hsr,y,hy,ny,hny,heq⟩ := (mem_check hM hx ht htop hr).mp hm r hr (hpre.1 r hr)
      exact ⟨s,hsc,hpre.2 s r q hsc hr hq hsr hrq,y,(hsucc y).mpr (Or.inl hy),ny,hny,heq⟩
    · exact ⟨r,hr,hrq,x,(hsucc x).mpr (Or.inr (fun _ => Iff.rfl)),nx,hx,heq⟩

theorem check_empty (hM : FirstOrder.Theory.Models M nativeZF) {t x name : M.Carrier .set}
    (hx : ForcingWithTopCarrier.Empty x) (hn : Checked t x name) : ForcingWithTopCarrier.Empty name := by
  intro z hz
  obtain ⟨y,_,hy,_,_⟩ := (ForcingCheckName.mem_checkName hM hn z).mp hz
  exact hx y hy

theorem check_hs (hM : FirstOrder.Theory.Models M nativeZF) (v : Fin 7 → M.Carrier .set)
    {I K B w G F t x name : M.Carrier .set}
    (hp : Presentation (v 0) I K B w (v 1) (v 2) (v 3) (v 4) (v 5) (v 6))
    (hG : ForcingLabelPermutations.Carrier I G) (hF : ForcingNormalFilter.Normal I G F)
    (ht : ForcingWithTopCarrier.Empty t) (hn : Checked t x name) :
    ForcingHS.HS actionFormula v G (v 6) F name := by
  have htW := (hp.2.2.2.2.2 t).mpr (Or.inl ht)
  have hf := ForcingProductFamily.family hM v hp hG
  apply ForcingHSCheck.check_hs hM actionFormula v G (v 6) F t hF.1 htW ?_ x name hn
  intro g hg
  obtain ⟨a,ha⟩ := hf.1 g hg
  exact ⟨a,ha,(hf.2 g a hg ha).1,
    Or.inl ⟨htW,ForcingProductFamily.top_fixed hp ht ((mapRel_action v g a).mp ha)⟩⟩

theorem forces_infinity (hM : FirstOrder.Theory.Models M nativeZF) {n : Nat}
    (env : Fin n → M.Carrier .set) (rho : Fin 7 → Fin n) (G F mul : Fin n)
    {I K B w p : M.Carrier .set}
    (hpresentation : Presentation (env (rho 0)) I K B w (env (rho 1)) (env (rho 2))
      (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hG : ForcingLabelPermutations.Carrier I (env G))
    (hF : ForcingNormalFilter.Normal I (env G) (env F))
    (hpre : PreorderOn (orderFormula (rho 0) mul) env (env (rho 6))) :
    Force (orderFormula (rho 0) mul) (domain rho G F) env Fin.elim0 (env (rho 6)) p Source.SetLanguage.infinity := by
  let R := orderFormula (rho 0) mul
  let H := domain rho G F
  let W := env (rho 6)
  obtain ⟨t,ht⟩ := ForcingWithTopCarrier.exists_empty hM
  have htW := (hpresentation.2.2.2.2.2 t).mpr (Or.inl ht)
  have htop : ∀ r, (Definitional.Project.FirstOrderSemantics.reduct M).mem r W → MapRel R env r t :=
    fun r _ => (orderFormula_semantics env (rho 0) mul r t).mpr (Or.inl ht)
  have hsChecked : ∀ x name, Checked t x name → ForcingClassEvaluation.Predicate H env name := by
    intro x name hn
    exact (domain_semantics env rho G F name).mpr
      (check_hs hM (fun j => env (rho j)) hpresentation hG hF ht hn)
  obtain ⟨omega,homega⟩ := SetTheory.ZF.exists_omega (ModelTransfer.project_models_iff.mp hM)
  obtain ⟨nw,hnw⟩ := ForcingCheckName.exists_checked hM t omega
  unfold Source.SetLanguage.infinity
  apply (ForcingFormula.force_ex R H env Fin.elim0 W p _).mpr
  intro q hq hqp
  refine ⟨q,hq,hpre.1 q hq,nw,hsChecked omega nw hnw,?_,?_⟩
  · apply (ForcingFormula.force_ex R H env _ W q _).mpr
    intro r hr hrq
    obtain ⟨zero,hzero,hzw⟩ := homega.1.1
    obtain ⟨nz,hnz⟩ := ForcingCheckName.exists_checked hM t zero
    refine ⟨r,hr,hpre.1 r hr,nz,hsChecked zero nz hnz,
      check_mem_of_mem hM hpre hnw hnz hzw htW htop hr,?_⟩
    change Force R H env (Fin.lastCases nz (Fin.lastCases nw Fin.elim0)) W r
      (.all (Formula.mem (2 : Fin 3) 1).neg)
    apply (ForcingFormula.force_all hM hpre hr _ _).mpr
    intro nu hnu
    apply (ForcingFormula.force_neg hM hpre hr _ _).mpr
    intro s hsc hsr hm
    exact ForcingBasicSetAxioms.not_mem_empty hM hpre (check_empty hM hzero hnz) hm
  · apply (ForcingFormula.force_all hM hpre hq _ _).mpr
    intro nu hnu
    apply (ForcingFormula.force_imp hM hpre hq _ _ _).mpr
    intro r hr hrq hm
    apply (ForcingFormula.force_ex R H env _ W r _).mpr
    intro a ha har
    obtain ⟨s,hsc,hsa,x,hx,nx,hnx,heq⟩ := (mem_check hM hnw htW htop hr).mp hm a ha har
    obtain ⟨succ,hsucc,hsw⟩ := homega.1.2 x hx
    obtain ⟨ns,hns⟩ := ForcingCheckName.exists_checked hM t succ
    refine ⟨s,hsc,hsa,ns,hsChecked succ ns hns,
      check_mem_of_mem hM hpre hnw hns hsw htW htop hsc,?_⟩
    change Force R H env (Fin.lastCases ns (Fin.lastCases nu (Fin.lastCases nw Fin.elim0))) W s
      (.all ((Formula.mem (3 : Fin 4) 2).iff ((Formula.mem 3 1).disj (Formula.equal 3 1))))
    apply (ForcingFormula.force_all hM hpre hsc _ _).mpr
    intro chi hchi
    rw [Source.Formula.iff,ForcingFormula.force_conj]
    constructor
    · apply (ForcingFormula.force_imp hM hpre hsc _ _ _).mpr
      intro b hb hbs hmem
      apply (ForcingFormula.force_disj R H env _ W b _ _).mpr
      intro c hc hcb
      obtain ⟨d,hd,hdc,hm | he⟩ := (check_successor hM hpre hnx hns hsucc htW htop hb).mp hmem c hc hcb
      · have hdn := ForcingAtomicBasic.eq_mono hM hpre hd (hpre.2 d b s hd hb hsc
          (hpre.2 d c b hd hc hb hdc hcb) hbs) heq
        exact ⟨d,hd,hdc,Or.inl ((ForcingAtomicLaws.mem_congr_right hM hpre hdn).mpr hm)⟩
      · have hdn := ForcingAtomicBasic.eq_mono hM hpre hd (hpre.2 d b s hd hb hsc
          (hpre.2 d c b hd hc hb hdc hcb) hbs) heq
        exact ⟨d,hd,hdc,Or.inr (ForcingAtomicLaws.eq_trans hM hpre he (ForcingAtomicBasic.eq_symm hM hdn))⟩
    · apply (ForcingFormula.force_imp hM hpre hsc _ _ _).mpr
      intro b hb hbs hdisj
      apply (check_successor hM hpre hnx hns hsucc htW htop hb).mpr
      intro c hc hcb
      obtain ⟨d,hd,hdc,hm | he⟩ := (ForcingFormula.force_disj R H env _ W b _ _).mp hdisj c hc hcb
      · have hdn := ForcingAtomicBasic.eq_mono hM hpre hd (hpre.2 d b s hd hb hsc
          (hpre.2 d c b hd hc hb hdc hcb) hbs) heq
        exact ⟨d,hd,hdc,Or.inl ((ForcingAtomicLaws.mem_congr_right hM hpre hdn).mp hm)⟩
      · have hdn := ForcingAtomicBasic.eq_mono hM hpre hd (hpre.2 d b s hd hb hsc
          (hpre.2 d c b hd hc hb hdc hcb) hbs) heq
        exact ⟨d,hd,hdc,Or.inr (ForcingAtomicLaws.eq_trans hM hpre he hdn)⟩

def sentence : Source.Sentence :=
  let rho : Fin 7 → Fin 16 := fun i => ⟨i.val, Nat.lt_trans i.isLt (by decide)⟩
  let R := orderFormula (0 : Fin 16) 13
  let H := domain rho 11 12
  ((ForcingDiagramPoset.leftCancelMonoid (0 : Fin 16) 13 14).imp
    ((ForcingProductFamily.presentation (0 : Fin 16) 7 8 9 10 1 2 3 4 5 6).imp
      ((ForcingLabelPermutations.carrier (7 : Fin 16) 11).imp
        ((ForcingNormalFilter.normal (7 : Fin 16) 11 12).imp
          (ForcingFormula.formula R H id Fin.elim0 6 15 Source.SetLanguage.infinity))))).close

theorem models (hM : FirstOrder.Theory.Models M nativeZF) : (Translation.sentence sentence).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro env hm hp hG hF
  let rho : Fin 7 → Fin 16 := fun i => ⟨i.val, Nat.lt_trans i.isLt (by decide)⟩
  let R := orderFormula (0 : Fin 16) 13
  let H := domain rho 11 12
  have hm' := (ForcingDiagramPoset.leftCancelMonoid_semantics (M := M) env 0 13 14).mp hm
  have hp' := (ForcingProductFamily.presentation_semantics (M := M) env 0 7 8 9 10 1 2 3 4 5 6).mp hp
  have hG' := (ForcingLabelPermutations.carrier_semantics (M := M) env 7 11).mp hG
  have hF' := (ForcingNormalFilter.normal_semantics (M := M) env 7 11 12).mp hF
  have hpre := ForcingProductPoset.preorder env 0 13 6 hm' hp'.2.2.2.2.1 hp'.2.2.2.1 hp'.2.2.2.2.2
  apply (ForcingFormula.formula_semantics (M := M) env R H id Fin.elim0 6 15 Source.SetLanguage.infinity).mpr
  have hzero : (fun i : Fin 0 => env (Fin.elim0 i)) = (Fin.elim0 : Fin 0 → M.Carrier .set) :=
    funext (fun i => Fin.elim0 i)
  rw [hzero]
  exact forces_infinity hM env rho 11 12 13 hp' hG' hF' hpre

theorem kernel_certificate : FirstOrder.Derives nativeZF [] (Translation.sentence sentence) :=
  ModelTransfer.derives (fun _ hM => models hM)

end PPAC.Migration.ForcingInfinity
