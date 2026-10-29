/- Pinned OrdinalCodes.selectionType_decide:180, ordF_not_mem_self:202,
selectedRank_eq_iff:212 and selectedRank_decide:229. Consumes the accepted
exact rank graph, its actual HS producer and full internal ordinal decision. -/
import PPAC.Migration.ForcingOrdinalDecision

namespace PPAC.Migration.ForcingOrdinalCoding
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open Source (Formula)
open ReplacementPredicates (paramsUp rel)
open ForcingMapConditions (MapRel)
open ForcingAtomicRelations (Forces forces)
open ForcingAtomicBasic (PreorderOn)
open ForcingCheckName (Checked checkName)
open ForcingRawRank (Ordinal Rank)
open ForcingClassEvaluation (Predicate)
open ForcingHS (HS)
open ForcingOrdinalRanks (Ranks)
open ForcingCollectedName (Collected)
open ForcingOrdinalTransitivity (OrdF)
open ForcingOrdinalDecision (Decision)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

section Consumers
variable (hM : FirstOrder.Theory.Models M nativeZF) {k j : Nat}
    {L : Formula (k+2)} {H : Formula (k+1)} {lp : Fin k → M.Carrier .set}
    {A : Formula (j+2)} {ap : Fin j → M.Carrier .set} {P top G F : M.Carrier .set}
    (hpre : PreorderOn L lp P) (ht : (Project.FirstOrderSemantics.reduct M).mem top P)
    (htop : ∀ q, (Project.FirstOrderSemantics.reduct M).mem q P → MapRel L lp q top)
    (hdomain : ∀ s, Predicate H lp s ↔ HS A ap G P F s)
    (hcheck : ∀ x nx, Checked top x nx → Predicate H lp nx)
include hM hpre ht htop hdomain hcheck

theorem selectionType_decide {n : Nat} {R : Formula (n+2)} {rp : Fin n → M.Carrier .set}
    {X order history selection p : M.Carrier .set}
    (hOrder : (Project.FirstOrderSemantics.reduct M).IsSetCodedWellOrder
      (KuratowskiZF.interpretation hM) order X)
    (hRanks : Ranks R rp X order P history) (hselection : Collected R rp X history P selection)
    (hs : Predicate H lp selection) (hp : (Project.FirstOrderSemantics.reduct M).mem p P) :
    ∃ a, Rank selection a ∧ Decision L lp P top selection p a := by
  obtain ⟨a,hra⟩ := ForcingRawRank.exists_rank hM selection
  exact ⟨a,hra,ForcingOrdinalDecision.ordF_eq_check_le hM hpre ht htop hdomain hcheck
    selection p a hs hp hra (ForcingOrdinalTransitivity.ordF_selectionType hM hpre hOrder hRanks hselection)⟩

theorem ordF_not_mem_self {sigma p : M.Carrier .set} (hs : Predicate H lp sigma)
    (ho : OrdF L H lp P p sigma) : ¬Forces false L lp P sigma sigma p := by
  intro hm
  have hp := ForcingAtomicBasic.condition hM hm
  obtain ⟨a,hra⟩ := ForcingRawRank.exists_rank hM sigma
  obtain ⟨q,hq,hqp,beta,hbeta,_,nb,hnb,he⟩ :=
    ForcingOrdinalDecision.ordF_eq_check_le hM hpre ht htop hdomain hcheck sigma p a hs hp hra ho
  have hqq := (ForcingAtomicLaws.mem_congr_right hM hpre he).mp
    ((ForcingAtomicLaws.mem_congr_left hM hpre he).mp (ForcingAtomicBasic.mem_mono hM hpre hq hqp hm))
  exact ForcingOrdinalDecision.ordinal_irrefl hM hbeta
    ((ForcingCheckReflection.mem_check_check hM hpre ht htop hq hnb hnb).mp hqq)

theorem selectedRank_eq_iff {n : Nat} {R : Formula (n+2)} {rp : Fin n → M.Carrier .set}
    {X order history a b na nb p : M.Carrier .set}
    (hOrder : (Project.FirstOrderSemantics.reduct M).IsSetCodedWellOrder
      (KuratowskiZF.interpretation hM) order X)
    (hRanks : Ranks R rp X order P history)
    (ha : (Project.FirstOrderSemantics.reduct M).mem a X) (hb : (Project.FirstOrderSemantics.reduct M).mem b X)
    (hna : PureKuratowski.PairMember M a na history) (hnb : PureKuratowski.PairMember M b nb history)
    (hsa : Predicate H lp na) (hsb : Predicate H lp nb)
    (hp : (Project.FirstOrderSemantics.reduct M).mem p P) (hRa : MapRel R rp a p) (hRb : MapRel R rp b p) :
    Forces true L lp P na nb p ↔ a = b := by
  constructor
  · intro he
    rcases hOrder.compare ha hb with hab | hab | hba
    · exact (ModelTransfer.extensionality hM).eq_of_same_members a b hab
    · have hm := ForcingOrdinalMembership.selectedRank_mem_selectedRank hM hpre hRanks ha hb hna hnb hab hp hRa
      exact False.elim (ordF_not_mem_self hM hpre ht htop hdomain hcheck hsa
        (ForcingOrdinalTransitivity.ordF_selectedRank hM hpre hOrder hRanks ha hna)
        ((ForcingAtomicLaws.mem_congr_right hM hpre he).mpr hm))
    · have hm := ForcingOrdinalMembership.selectedRank_mem_selectedRank hM hpre hRanks hb ha hnb hna hba hp hRb
      exact False.elim (ordF_not_mem_self hM hpre ht htop hdomain hcheck hsb
        (ForcingOrdinalTransitivity.ordF_selectedRank hM hpre hOrder hRanks hb hnb)
        ((ForcingAtomicLaws.mem_congr_right hM hpre he).mp hm))
  · intro he
    subst b
    obtain ⟨value,_,hv⟩ := hRanks.1.2 a ha
    have heq : na = nb := (hv na hna).trans (hv nb hnb).symm
    exact heq ▸ ForcingAtomicBasic.eq_refl hM hpre na p hp

theorem selectedRank_decide {n : Nat} {R : Formula (n+2)} {rp : Fin n → M.Carrier .set}
    {X order history selection a name theta ntheta p : M.Carrier .set}
    (hOrder : (Project.FirstOrderSemantics.reduct M).IsSetCodedWellOrder
      (KuratowskiZF.interpretation hM) order X)
    (hRanks : Ranks R rp X order P history) (hselection : Collected R rp X history P selection)
    (ha : (Project.FirstOrderSemantics.reduct M).mem a X) (han : PureKuratowski.PairMember M a name history)
    (hs : Predicate H lp name) (hp : (Project.FirstOrderSemantics.reduct M).mem p P) (hR : MapRel R rp a p)
    (hntheta : Checked top theta ntheta) (htheta : Forces true L lp P selection ntheta p) :
    ∃ q, (Project.FirstOrderSemantics.reduct M).mem q P ∧ MapRel L lp q p ∧
      ∃ beta, Ordinal beta ∧ (Project.FirstOrderSemantics.reduct M).mem beta theta ∧
        ∃ nb, Checked top beta nb ∧ Forces true L lp P name nb q := by
  obtain ⟨aRank,hRank⟩ := ForcingRawRank.exists_rank hM name
  obtain ⟨q,hq,hqp,beta,hbeta,_,nb,hnb,he⟩ :=
    ForcingOrdinalDecision.ordF_eq_check_le hM hpre ht htop hdomain hcheck name p aRank hs hp hRank
      (ForcingOrdinalTransitivity.ordF_selectedRank hM hpre hOrder hRanks ha han)
  have hm := ForcingAtomicBasic.mem_mono hM hpre hq hqp
    (ForcingOrdinalMembership.selectedRank_mem_selectionType hM hpre hselection ha han hp hR)
  have hm' := (ForcingAtomicLaws.mem_congr_right hM hpre (ForcingAtomicBasic.eq_mono hM hpre hq hqp htheta)).mp
    ((ForcingAtomicLaws.mem_congr_left hM hpre he).mp hm)
  exact ⟨q,hq,hqp,beta,hbeta,(ForcingCheckReflection.mem_check_check hM hpre ht htop hq hnb hntheta).mp hm',nb,hnb,he⟩
end Consumers

def typeDecision {k m : Nat} (L : Formula (k+2)) (lp : Fin k → Fin m)
    (P top name p : Fin m) : Formula m := .ex
  ((LayerRankSyntax.rank name.castSucc (Fin.last m)).conj
    (ForcingOrdinalDecision.decision L (paramsUp lp) P.castSucc top.castSucc name.castSucc p.castSucc (Fin.last m)))

theorem typeDecision_semantics {k m : Nat} (env : Fin m → M.Carrier .set)
    (L : Formula (k+2)) (lp : Fin k → Fin m) (P top name p : Fin m) :
    Formula.Realize (Project.FirstOrderSemantics.reduct M).mem env (typeDecision L lp P top name p) ↔
      ∃ a, Rank (env name) a ∧ Decision L (fun i => env (lp i)) (env P) (env top) (env name) (env p) a := by
  simp only [typeDecision,Formula.Realize,ForcingRawRank.rank_semantics (M := M),
    ForcingOrdinalDecision.decision_semantics (M := M),paramsUp,Fin.lastCases_last,Fin.lastCases_castSucc]
  rfl

def lowerDecision {k m : Nat} (L : Formula (k+2)) (lp : Fin k → Fin m)
    (P top name theta p : Fin m) : Formula m :=
  let up : Fin m → Fin (m+3) := fun i => i.castSucc.castSucc.castSucc
  let q := (Fin.last m).castSucc.castSucc
  let beta := (Fin.last (m+1)).castSucc
  let nb := Fin.last (m+2)
  .ex (.ex (.ex ((Formula.mem q (up P)).conj ((rel L (fun i => up (lp i)) q (up p)).conj
    ((OrdinalSyntax.ordinal beta).conj ((Formula.mem beta (up theta)).conj
      ((checkName (up top) beta nb).conj (forces true L (fun i => up (lp i)) (up P) (up name) nb q))))))))

theorem lowerDecision_semantics {k m : Nat} (env : Fin m → M.Carrier .set)
    (L : Formula (k+2)) (lp : Fin k → Fin m) (P top name theta p : Fin m) :
    Formula.Realize (Project.FirstOrderSemantics.reduct M).mem env (lowerDecision L lp P top name theta p) ↔
      ∃ q, (Project.FirstOrderSemantics.reduct M).mem q (env P) ∧ MapRel L (fun i => env (lp i)) q (env p) ∧
        ∃ beta, Ordinal beta ∧ (Project.FirstOrderSemantics.reduct M).mem beta (env theta) ∧
          ∃ nb, Checked (env top) beta nb ∧ Forces true L (fun i => env (lp i)) (env P) (env name) nb q := by
  simp only [lowerDecision,Formula.Realize,ForcingRawRank.ordinal_semantics (M := M),
    ForcingMapConditions.rel_semantics (M := M),ForcingCheckName.checkName_semantics (M := M),
    ForcingAtomicRelations.forces_semantics (M := M),Fin.lastCases_last,Fin.lastCases_castSucc]
  constructor
  · rintro ⟨q,beta,nb,hq,hqp,hbeta,hbt,hnb,he⟩
    exact ⟨q,hq,hqp,beta,hbeta,hbt,nb,hnb,he⟩
  · rintro ⟨q,hq,hqp,beta,hbeta,hbt,nb,hnb,he⟩
    exact ⟨q,beta,nb,hq,hqp,hbeta,hbt,hnb,he⟩

def selectedInput {n m : Nat} (R : Formula (n+2)) (rp : Fin n → Fin m)
    (X history a name p : Fin m) : Formula m :=
  (Formula.mem a X).conj ((Source.SetLanguage.edge history a name).conj (rel R rp a p))

def codingBody {n m : Nat} (R : Formula (n+2)) (rp : Fin n → Fin m) (ra : Fin 7 → Fin m)
    (I K B w G F support X order history selection mul unit top p a b na nb theta ntheta : Fin m) : Formula m :=
  let L := ForcingProductSymmetry.orderFormula (ra 0) mul
  (ForcingOrdinalFixed.context R rp ra I K B w G F support X).imp
    ((ForcingDiagramPoset.leftCancelMonoid (ra 0) mul unit).imp ((ForcingWithTopCarrier.empty top).imp
      ((ForcingOrdinalRanks.ranks R rp X order (ra 6) history).imp
        ((ForcingCollectedName.collected R rp X history (ra 6) selection).imp ((Formula.mem p (ra 6)).imp
          ((typeDecision L id (ra 6) top selection p).conj
            ((selectedInput R rp X history a na p).imp
              ((forces false L id (ra 6) na na p).neg.conj
                (((selectedInput R rp X history b nb p).imp ((forces true L id (ra 6) na nb p).iff (.equal a b))).conj
                  ((checkName top theta ntheta).imp ((forces true L id (ra 6) selection ntheta p).imp
                    (lowerDecision L id (ra 6) top na theta p))))))))))))

def codingSentence {n m : Nat} (R : Formula (n+2)) (rp : Fin n → Fin m) (ra : Fin 7 → Fin m)
    (I K B w G F support X order history selection mul unit top p a b na nb theta ntheta : Fin m) : Project.Sentence where
  formula := Project.Formula.forallClosure m (.imp
    (Project.Formula.isSetCodedWellOrder PureKuratowskiProject.convention (.bound order) (.bound X))
    (ProjectSyntax.encode id (codingBody R rp ra I K B w G F support X order history selection mul unit top p a b na nb theta ntheta)))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed]

theorem coding_models {n m : Nat} (R : Formula (n+2)) (rp : Fin n → Fin m) (ra : Fin 7 → Fin m)
    (I K B w G F support X order history selection mul unit top p a b na nb theta ntheta : Fin m)
    (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (codingSentence R rp ra I K B w G F support X order history selection mul unit top p a b na nb theta ntheta)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro env
  simp only [Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_isSetCodedWellOrder_iff (KuratowskiZF.interpretation hM),Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),codingBody,selectedInput,Source.Formula.iff,
    Source.Formula.neg,Formula.Realize,ForcingOrdinalFixed.context_semantics (M := M),
    ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),ForcingWithTopCarrier.empty_semantics (M := M),
    ForcingOrdinalRanks.ranks_semantics (M := M),ForcingCollectedName.collected_semantics (M := M),
    typeDecision_semantics (M := M),lowerDecision_semantics (M := M),ForcingAtomicRelations.forces_semantics (M := M),
    ForcingMapConditions.rel_semantics (M := M),ForcingCheckName.checkName_semantics (M := M),KuratowskiZF.source_edge]
  rintro hOrder ⟨hpres,hG,hF,hSupport,hSF,hInv⟩ hmonoid ht hRanks hselection hp
  let L := ForcingProductSymmetry.orderFormula (ra 0) mul
  let H := ForcingPairUnion.domain ra G F
  have hpre := ForcingProductPoset.preorder env (ra 0) mul (ra 6) hmonoid
    hpres.2.2.2.2.1 hpres.2.2.2.1 hpres.2.2.2.2.2
  have htP := (hpres.2.2.2.2.2 (env top)).mpr (Or.inl ht)
  have htop : ∀ q, (Project.FirstOrderSemantics.reduct M).mem q (env (ra 6)) → MapRel L env q (env top) :=
    fun q _ => (ForcingProductSymmetry.orderFormula_semantics env (ra 0) mul q (env top)).mpr (Or.inl ht)
  have hdomain := fun s => ForcingPairUnion.domain_semantics env ra G F s
  have hcheck : ∀ x nx, Checked (env top) x nx → Predicate H env nx := by
    intro x nx hn
    exact (hdomain nx).mpr (ForcingInfinity.check_hs hM (fun i => env (ra i)) hpres hG hF ht hn)
  have hFamily := ForcingOrdinalFixed.ranks_fixed hM R (fun i => env (rp i)) (fun i => env (ra i))
    hpres hG hF hSupport hSF hInv hOrder hRanks
  have hSelection := ForcingOrdinalFixed.collected_fixed hM R (fun i => env (rp i)) (fun i => env (ra i))
    hpres hG hF hSupport hSF hFamily hInv hselection
  refine ⟨selectionType_decide hM hpre htP htop hdomain hcheck hOrder hRanks hselection
    ((hdomain (env selection)).mpr hSelection.1) hp,?_⟩
  rintro ⟨ha,han,hRa⟩
  have hsa := (hdomain (env na)).mpr (hFamily (env a) ha (env na) han).1
  refine ⟨ordF_not_mem_self hM hpre htP htop hdomain hcheck hsa
    (ForcingOrdinalTransitivity.ordF_selectedRank hM hpre hOrder hRanks ha han),?_,?_⟩
  · rintro ⟨hb,hbn,hRb⟩
    have hsb := (hdomain (env nb)).mpr (hFamily (env b) hb (env nb) hbn).1
    have he := selectedRank_eq_iff hM hpre htP htop hdomain hcheck hOrder hRanks ha hb han hbn hsa hsb hp hRa hRb
    exact ⟨he.mp,he.mpr⟩
  · intro hntheta htheta
    exact selectedRank_decide hM hpre htP htop hdomain hcheck hOrder hRanks hselection ha han hsa hp hRa hntheta htheta

theorem coding_kernel_certificate {n m : Nat} (R : Formula (n+2)) (rp : Fin n → Fin m) (ra : Fin 7 → Fin m)
    (I K B w G F support X order history selection mul unit top p a b na nb theta ntheta : Fin m) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence
      (codingSentence R rp ra I K B w G F support X order history selection mul unit top p a b na nb theta ntheta)) :=
  ModelTransfer.derives (fun _ hM => coding_models R rp ra I K B w G F support X order history selection mul unit top p a b na nb theta ntheta hM)

end PPAC.Migration.ForcingOrdinalCoding
