/- Pinned PersistentCodes.TransF/OrdF and OrdinalCodes transF/ordF laws.
The unrestricted name-domain formula is retained; OrdF is the source
auxiliary hereditary transitivity property, not the ACwo ordinal formula. -/
import PPAC.Migration.ForcingOrdinalMembership

namespace PPAC.Migration.ForcingOrdinalTransitivity
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open Source (Formula)
open ReplacementPredicates (paramsUp rel)
open ForcingMapConditions (MapRel)
open ForcingAtomicRelations (Forces forces)
open ForcingAtomicBasic (PreorderOn)
open ForcingClassEvaluation (Predicate)
open ForcingCollectedName (Collected)
open ForcingOrdinalRanks (Ranks)
open ForcingOrdinalMembership
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def TransF {k : Nat} (L : Formula (k+2)) (H : Formula (k+1))
    (lp : Fin k → M.Carrier .set) (P p name : M.Carrier .set) : Prop :=
  ∀ nu, Predicate H lp nu → ∀ chi, Predicate H lp chi → ∀ q,
    (Project.FirstOrderSemantics.reduct M).mem q P → MapRel L lp q p →
    Forces false L lp P nu name q → Forces false L lp P chi nu q →
    Forces false L lp P chi name q

def OrdF {k : Nat} (L : Formula (k+2)) (H : Formula (k+1))
    (lp : Fin k → M.Carrier .set) (P p name : M.Carrier .set) : Prop :=
  TransF L H lp P p name ∧ ∀ nu, Predicate H lp nu → ∀ q,
    (Project.FirstOrderSemantics.reduct M).mem q P → MapRel L lp q p →
    Forces false L lp P nu name q → TransF L H lp P q nu

def transF {k m : Nat} (L : Formula (k+2)) (H : Formula (k+1)) (lp : Fin k → Fin m)
    (P p name : Fin m) : Formula m :=
  let up : Fin m → Fin (m+3) := fun i => i.castSucc.castSucc.castSucc
  let nu := (Fin.last m).castSucc.castSucc
  let chi := (Fin.last (m+1)).castSucc
  let q := Fin.last (m+2)
  .all ((MinimalPredicates.pred H (paramsUp lp) (Fin.last m)).imp (.all
    ((MinimalPredicates.pred H (paramsUp (paramsUp lp)) (Fin.last (m+1))).imp (.all
      ((Formula.mem q (up P)).imp ((rel L (fun i => up (lp i)) q (up p)).imp
        ((forces false L (fun i => up (lp i)) (up P) nu (up name) q).imp
          ((forces false L (fun i => up (lp i)) (up P) chi nu q).imp
            (forces false L (fun i => up (lp i)) (up P) chi (up name) q)))))))))

theorem transF_semantics {k m : Nat} (env : Fin m → M.Carrier .set)
    (L : Formula (k+2)) (H : Formula (k+1)) (lp : Fin k → Fin m) (P p name : Fin m) :
    Formula.Realize (Project.FirstOrderSemantics.reduct M).mem env (transF L H lp P p name) ↔
      TransF L H (fun i => env (lp i)) (env P) (env p) (env name) := by
  simp only [transF,TransF,Formula.Realize,ForcingClassEvaluation.predicate_semantics (M := M),
    ForcingMapConditions.rel_semantics (M := M),ForcingAtomicRelations.forces_semantics (M := M),
    paramsUp,Fin.lastCases_last,Fin.lastCases_castSucc]
  rfl

def ordF {k m : Nat} (L : Formula (k+2)) (H : Formula (k+1)) (lp : Fin k → Fin m)
    (P p name : Fin m) : Formula m :=
  (transF L H lp P p name).conj (.all
    ((MinimalPredicates.pred H (paramsUp lp) (Fin.last m)).imp (.all
      ((Formula.mem (Fin.last (m+1)) P.castSucc.castSucc).imp
        ((rel L (paramsUp (paramsUp lp)) (Fin.last (m+1)) p.castSucc.castSucc).imp
          ((forces false L (paramsUp (paramsUp lp)) P.castSucc.castSucc
            (Fin.last m).castSucc name.castSucc.castSucc (Fin.last (m+1))).imp
            (transF L H (paramsUp (paramsUp lp)) P.castSucc.castSucc
              (Fin.last (m+1)) (Fin.last m).castSucc)))))))

theorem ordF_semantics {k m : Nat} (env : Fin m → M.Carrier .set)
    (L : Formula (k+2)) (H : Formula (k+1)) (lp : Fin k → Fin m) (P p name : Fin m) :
    Formula.Realize (Project.FirstOrderSemantics.reduct M).mem env (ordF L H lp P p name) ↔
      OrdF L H (fun i => env (lp i)) (env P) (env p) (env name) := by
  simp only [ordF,OrdF,Formula.Realize,transF_semantics (M := M),
    ForcingClassEvaluation.predicate_semantics (M := M),ForcingMapConditions.rel_semantics (M := M),
    ForcingAtomicRelations.forces_semantics (M := M),paramsUp,Fin.lastCases_last,Fin.lastCases_castSucc]
  rfl

theorem transF_mono {k : Nat} {L : Formula (k+2)} {H : Formula (k+1)}
    {lp : Fin k → M.Carrier .set} {P p q name : M.Carrier .set}
    (hpre : PreorderOn L lp P) (hp : (Project.FirstOrderSemantics.reduct M).mem p P)
    (hq : (Project.FirstOrderSemantics.reduct M).mem q P) (hqp : MapRel L lp q p)
    (ht : TransF L H lp P p name) : TransF L H lp P q name :=
  fun nu hnu chi hchi r hr hrq => ht nu hnu chi hchi r hr (hpre.2 r q p hr hq hp hrq hqp)

theorem transF_congr (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    {L : Formula (k+2)} {H : Formula (k+1)} {lp : Fin k → M.Carrier .set}
    {P p sigma tau : M.Carrier .set} (hpre : PreorderOn L lp P)
    (he : Forces true L lp P sigma tau p) : TransF L H lp P p sigma ↔ TransF L H lp P p tau := by
  have forward {sigma tau : M.Carrier .set} (he : Forces true L lp P sigma tau p)
      (ht : TransF L H lp P p sigma) : TransF L H lp P p tau := by
    intro nu hnu chi hchi q hq hqp hnuM hchiM
    have hem := ForcingAtomicBasic.eq_mono hM hpre hq hqp he
    exact (ForcingAtomicLaws.mem_congr_right hM hpre hem).mp
      (ht nu hnu chi hchi q hq hqp
        ((ForcingAtomicLaws.mem_congr_right hM hpre hem).mpr hnuM) hchiM)
  exact ⟨forward he,forward (ForcingAtomicBasic.eq_symm hM he)⟩

theorem ordF_mono {k : Nat} {L : Formula (k+2)} {H : Formula (k+1)}
    {lp : Fin k → M.Carrier .set} {P p q name : M.Carrier .set}
    (hpre : PreorderOn L lp P) (hp : (Project.FirstOrderSemantics.reduct M).mem p P)
    (hq : (Project.FirstOrderSemantics.reduct M).mem q P) (hqp : MapRel L lp q p)
    (ho : OrdF L H lp P p name) : OrdF L H lp P q name :=
  ⟨transF_mono hpre hp hq hqp ho.1,
    fun nu hnu r hr hrq => ho.2 nu hnu r hr (hpre.2 r q p hr hq hp hrq hqp)⟩

theorem ordF_congr (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    {L : Formula (k+2)} {H : Formula (k+1)} {lp : Fin k → M.Carrier .set}
    {P p sigma tau : M.Carrier .set} (hpre : PreorderOn L lp P)
    (he : Forces true L lp P sigma tau p) : OrdF L H lp P p sigma ↔ OrdF L H lp P p tau := by
  have forward {sigma tau : M.Carrier .set} (he : Forces true L lp P sigma tau p)
      (ho : OrdF L H lp P p sigma) : OrdF L H lp P p tau := by
    refine ⟨(transF_congr hM hpre he).mp ho.1,?_⟩
    intro nu hnu q hq hqp hm
    exact ho.2 nu hnu q hq hqp ((ForcingAtomicLaws.mem_congr_right hM hpre
      (ForcingAtomicBasic.eq_mono hM hpre hq hqp he)).mpr hm)
  exact ⟨forward he,forward (ForcingAtomicBasic.eq_symm hM he)⟩

theorem ordF_mem (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    {L : Formula (k+2)} {H : Formula (k+1)} {lp : Fin k → M.Carrier .set}
    {P p sigma tau : M.Carrier .set} (hpre : PreorderOn L lp P)
    (htau : Predicate H lp tau) (ho : OrdF L H lp P p sigma)
    (hm : Forces false L lp P tau sigma p) : OrdF L H lp P p tau := by
  have hp := ForcingAtomicBasic.condition hM hm
  refine ⟨ho.2 tau htau p hp (hpre.1 p hp) hm,?_⟩
  intro nu hnu q hq hqp hnuM
  exact ho.2 nu hnu q hq hqp (ho.1 tau htau nu hnu q hq hqp
    (ForcingAtomicBasic.mem_mono hM hpre hq hqp hm) hnuM)

/-- Exact source transitiveSet formula over the unchanged name domain. -/
theorem forces_transitiveSet (hM : FirstOrder.Theory.Models M nativeZF) {k n : Nat}
    {L : Formula (k+2)} {H : Formula (k+1)} {lp : Fin k → M.Carrier .set}
    {P p : M.Carrier .set} (hpre : PreorderOn L lp P)
    (hp : (Project.FirstOrderSemantics.reduct M).mem p P)
    (v : Fin n → M.Carrier .set) (x : Fin n) :
    ForcingFormula.Force L H lp v P p (Source.SetLanguage.transitiveSet x) ↔ TransF L H lp P p (v x) := by
  unfold Source.SetLanguage.transitiveSet
  rw [ForcingSound.rename hM hpre _ _ _ _ hp]
  constructor
  · intro h nu hnu chi hchi q hq hqp hnuM hchiM
    have hn := (ForcingFormula.force_all hM hpre hp _ _).mp h nu hnu
    have hc := (ForcingFormula.force_all hM hpre hp _ _).mp hn chi hchi
    have hi := (ForcingFormula.force_imp hM hpre hp _ _ _).mp hc q hq hqp hnuM
    exact (ForcingFormula.force_imp hM hpre hq _ _ _).mp hi q hq (hpre.1 q hq) hchiM
  · intro h
    apply (ForcingFormula.force_all hM hpre hp _ _).mpr
    intro nu hnu
    apply (ForcingFormula.force_all hM hpre hp _ _).mpr
    intro chi hchi
    apply (ForcingFormula.force_imp hM hpre hp _ _ _).mpr
    intro q hq hqp hnuM
    apply (ForcingFormula.force_imp hM hpre hq _ _ _).mpr
    intro r hr hrq hchiM
    exact h nu hnu chi hchi r hr (hpre.2 r q p hr hq hp hrq hqp)
      (ForcingAtomicBasic.mem_mono hM hpre hr hrq hnuM) hchiM

/-- The full source ordinal formula implies the auxiliary OrdF, not conversely. -/
theorem ordF_of_forces_ordinal (hM : FirstOrder.Theory.Models M nativeZF) {k n : Nat}
    {L : Formula (k+2)} {H : Formula (k+1)} {lp : Fin k → M.Carrier .set}
    {P p : M.Carrier .set} (hpre : PreorderOn L lp P)
    (hp : (Project.FirstOrderSemantics.reduct M).mem p P)
    (v : Fin n → M.Carrier .set) (x : Fin n)
    (ho : ForcingFormula.Force L H lp v P p (Source.SetLanguage.ordinal x)) : OrdF L H lp P p (v x) := by
  have ht := (forces_transitiveSet hM hpre hp v x).mp ho.1
  have hl : ForcingFormula.Force L H lp v P p (Source.SetLanguage.membershipLinear x) := ho.2.1
  unfold Source.SetLanguage.membershipLinear at hl
  rw [ForcingSound.rename hM hpre _ _ _ _ hp] at hl
  refine ⟨ht,?_⟩
  intro tau htau q hq hqp htauM nu hnu chi hchi r hr hrq hnuM hchiM
  have hrp := hpre.2 r q p hr hq hp hrq hqp
  have htauM' := ForcingAtomicBasic.mem_mono hM hpre hr hrq htauM
  have hnuM' := ht tau htau nu hnu r hr hrp htauM' hnuM
  have hchiM' := ht nu hnu chi hchi r hr hrp hnuM' hchiM
  have h1 := (ForcingFormula.force_all hM hpre hp _ _).mp hl.2.1 chi hchi
  have h2 := (ForcingFormula.force_all hM hpre hp _ _).mp h1 nu hnu
  have h3 := (ForcingFormula.force_all hM hpre hp _ _).mp h2 tau htau
  have h4 := (ForcingFormula.force_imp hM hpre hp _ _ _).mp h3 r hr hrp hchiM'
  have h5 := (ForcingFormula.force_imp hM hpre hr _ _ _).mp h4 r hr (hpre.1 r hr) hnuM'
  have h6 := (ForcingFormula.force_imp hM hpre hr _ _ _).mp h5 r hr (hpre.1 r hr) htauM'
  exact (ForcingFormula.force_imp hM hpre hr _ _ _).mp h6 r hr (hpre.1 r hr) ⟨hchiM,hnuM⟩

theorem transF_selectedRank (hM : FirstOrder.Theory.Models M nativeZF) {k n : Nat}
    {L : Formula (k+2)} {H : Formula (k+1)} {lp : Fin k → M.Carrier .set}
    {R : Formula (n+2)} {rp : Fin n → M.Carrier .set}
    {P X order history a name p : M.Carrier .set}
    (hpre : PreorderOn L lp P)
    (hOrder : (Project.FirstOrderSemantics.reduct M).IsSetCodedWellOrder
      (KuratowskiZF.interpretation hM) order X)
    (hRanks : Ranks R rp X order P history)
    (ha : (Project.FirstOrderSemantics.reduct M).mem a X)
    (han : PureKuratowski.PairMember M a name history) : TransF L H lp P p name := by
  intro nu _ chi _ q hq _ hnu hchi
  apply ForcingAtomicBasic.mem_of_dense hM hpre hq
  intro r hr hrq
  obtain ⟨s,b,c,child,hs,hsr,hb,hba,_,hbc,_,_,he⟩ :=
    (mem_selectedRank hM L lp R rp hRanks ha han hq).mp hnu r hr hrq
  have hsq := hpre.2 s r q hs hr hq hsr hrq
  have hm := (ForcingAtomicLaws.mem_congr_right hM hpre he).mp
    (ForcingAtomicBasic.mem_mono hM hpre hs hsq hchi)
  exact ⟨s,hs,hsr,rank_inclusion hM hOrder hRanks hb ha hbc han (Or.inr hba) hm⟩

theorem transF_selectionType (hM : FirstOrder.Theory.Models M nativeZF) {k n : Nat}
    {L : Formula (k+2)} {H : Formula (k+1)} {lp : Fin k → M.Carrier .set}
    {R : Formula (n+2)} {rp : Fin n → M.Carrier .set}
    {P X order history selection p : M.Carrier .set}
    (hpre : PreorderOn L lp P) (hRanks : Ranks R rp X order P history)
    (hselection : Collected R rp X history P selection) : TransF L H lp P p selection := by
  intro nu _ chi _ q hq _ hnu hchi
  apply ForcingAtomicBasic.mem_of_dense hM hpre hq
  intro r hr hrq
  obtain ⟨s,b,c,child,hs,hsr,hb,_,_,hbc,_,_,he⟩ :=
    (mem_selectionType hM L lp R rp (order := order) (a := selection) hselection hq).mp hnu r hr hrq
  have hm := (ForcingAtomicLaws.mem_congr_right hM hpre he).mp
    (ForcingAtomicBasic.mem_mono hM hpre hs (hpre.2 s r q hs hr hq hsr hrq) hchi)
  exact ⟨s,hs,hsr,type_inclusion hM hRanks hselection hb hbc hm⟩

theorem ordF_selectedRank (hM : FirstOrder.Theory.Models M nativeZF) {k n : Nat}
    {L : Formula (k+2)} {H : Formula (k+1)} {lp : Fin k → M.Carrier .set}
    {R : Formula (n+2)} {rp : Fin n → M.Carrier .set}
    {P X order history a name p : M.Carrier .set}
    (hpre : PreorderOn L lp P)
    (hOrder : (Project.FirstOrderSemantics.reduct M).IsSetCodedWellOrder
      (KuratowskiZF.interpretation hM) order X)
    (hRanks : Ranks R rp X order P history)
    (ha : (Project.FirstOrderSemantics.reduct M).mem a X)
    (han : PureKuratowski.PairMember M a name history) : OrdF L H lp P p name := by
  refine ⟨transF_selectedRank hM hpre hOrder hRanks ha han,?_⟩
  intro nu _ q hq _ hnu chi hchi psi hpsi r hr hrq hchiM hpsiM
  apply ForcingAtomicBasic.mem_of_dense hM hpre hr
  intro s hs hsr
  obtain ⟨t,b,c,child,ht,hts,hb,_,_,hbc,_,_,he⟩ :=
    (mem_selectedRank hM L lp R rp hRanks ha han hq).mp hnu s hs (hpre.2 s r q hs hr hq hsr hrq)
  have htrans := (transF_congr hM (H := H) hpre he).mpr (transF_selectedRank hM hpre hOrder hRanks hb hbc)
  have htr := hpre.2 t s r ht hs hr hts hsr
  exact ⟨t,ht,hts,htrans chi hchi psi hpsi t ht (hpre.1 t ht)
    (ForcingAtomicBasic.mem_mono hM hpre ht htr hchiM)
    (ForcingAtomicBasic.mem_mono hM hpre ht htr hpsiM)⟩

theorem ordF_selectionType (hM : FirstOrder.Theory.Models M nativeZF) {k n : Nat}
    {L : Formula (k+2)} {H : Formula (k+1)} {lp : Fin k → M.Carrier .set}
    {R : Formula (n+2)} {rp : Fin n → M.Carrier .set}
    {P X order history selection p : M.Carrier .set}
    (hpre : PreorderOn L lp P)
    (hOrder : (Project.FirstOrderSemantics.reduct M).IsSetCodedWellOrder
      (KuratowskiZF.interpretation hM) order X)
    (hRanks : Ranks R rp X order P history)
    (hselection : Collected R rp X history P selection) : OrdF L H lp P p selection := by
  refine ⟨transF_selectionType hM hpre hRanks hselection,?_⟩
  intro nu _ q hq _ hnu chi hchi psi hpsi r hr hrq hchiM hpsiM
  apply ForcingAtomicBasic.mem_of_dense hM hpre hr
  intro s hs hsr
  obtain ⟨t,b,c,child,ht,hts,hb,_,_,hbc,_,_,he⟩ :=
    (mem_selectionType hM L lp R rp (order := order) (a := selection) hselection hq).mp hnu s hs
      (hpre.2 s r q hs hr hq hsr hrq)
  have htrans := (transF_congr hM (H := H) hpre he).mpr (transF_selectedRank hM hpre hOrder hRanks hb hbc)
  have htr := hpre.2 t s r ht hs hr hts hsr
  exact ⟨t,ht,hts,htrans chi hchi psi hpsi t ht (hpre.1 t ht)
    (ForcingAtomicBasic.mem_mono hM hpre ht htr hchiM)
    (ForcingAtomicBasic.mem_mono hM hpre ht htr hpsiM)⟩

def rankBody {k n m : Nat} (L : Formula (k+2)) (H : Formula (k+1)) (lp : Fin k → Fin m)
    (R : Formula (n+2)) (rp : Fin n → Fin m) (P X order history a name p : Fin m) : Formula m :=
  (ForcingAtomicBasic.preorder L lp P).imp
    ((ForcingOrdinalRanks.ranks R rp X order P history).imp ((Formula.mem a X).imp
      ((Source.SetLanguage.edge history a name).imp (ordF L H lp P p name))))

def typeBody {k n m : Nat} (L : Formula (k+2)) (H : Formula (k+1)) (lp : Fin k → Fin m)
    (R : Formula (n+2)) (rp : Fin n → Fin m) (P X order history selection p : Fin m) : Formula m :=
  (ForcingAtomicBasic.preorder L lp P).imp
    ((ForcingOrdinalRanks.ranks R rp X order P history).imp
      ((ForcingCollectedName.collected R rp X history P selection).imp (ordF L H lp P p selection)))

def ordinalSentence {k n m : Nat} (initial : Bool)
    (L : Formula (k+2)) (H : Formula (k+1)) (lp : Fin k → Fin m)
    (R : Formula (n+2)) (rp : Fin n → Fin m) (P X order history a name p : Fin m) : Project.Sentence where
  formula := Project.Formula.forallClosure m (.imp
    (Project.Formula.isSetCodedWellOrder PureKuratowskiProject.convention (.bound order) (.bound X))
    (ProjectSyntax.encode id (if initial then rankBody L H lp R rp P X order history a name p
      else typeBody L H lp R rp P X order history name p)))
  freeClosed := by
    split <;> simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed]

theorem ordinal_models {k n m : Nat} (initial : Bool)
    (L : Formula (k+2)) (H : Formula (k+1)) (lp : Fin k → Fin m)
    (R : Formula (n+2)) (rp : Fin n → Fin m) (P X order history a name p : Fin m)
    (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (ordinalSentence initial L H lp R rp P X order history a name p)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  cases initial <;> simp only [Bool.false_eq_true,ite_false,ite_true,
    Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_isSetCodedWellOrder_iff (KuratowskiZF.interpretation hM),Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),rankBody,typeBody,Formula.Realize,
    ForcingAtomicBasic.preorder_semantics (M := M),ForcingOrdinalRanks.ranks_semantics (M := M),
    ForcingCollectedName.collected_semantics (M := M),KuratowskiZF.source_edge,ordF_semantics (M := M)]
  · intro hOrder hpre hRanks hs
    exact ordF_selectionType hM hpre hOrder hRanks hs
  · intro hOrder hpre hRanks ha han
    exact ordF_selectedRank hM hpre hOrder hRanks ha han

/-- Both source OrdF conclusions in the original pure membership proof kernel. -/
theorem ordinal_kernel_certificate {k n m : Nat} (initial : Bool)
    (L : Formula (k+2)) (H : Formula (k+1)) (lp : Fin k → Fin m)
    (R : Formula (n+2)) (rp : Fin n → Fin m) (P X order history a name p : Fin m) :
    FirstOrder.Derives nativeZF []
      (Project.fo_sentence (ordinalSentence initial L H lp R rp P X order history a name p)) :=
  ModelTransfer.derives (fun _ hM => ordinal_models initial L H lp R rp P X order history a name p hM)

def formulaBridgeSentence {k n m : Nat} (L : Formula (k+2)) (H : Formula (k+1))
    (lp : Fin k → Fin m) (v : Fin n → Fin m) (P p : Fin m) (x : Fin n) : Source.Sentence :=
  ((ForcingAtomicBasic.preorder L lp P).imp ((Formula.mem p P).imp
    (((ForcingFormula.formula L H lp v P p (Source.SetLanguage.transitiveSet x)).iff
      (transF L H lp P p (v x))).conj
      ((ForcingFormula.formula L H lp v P p (Source.SetLanguage.ordinal x)).imp
        (ordF L H lp P p (v x)))))).close

theorem formula_bridge_models {k n m : Nat} (L : Formula (k+2)) (H : Formula (k+1))
    (lp : Fin k → Fin m) (v : Fin n → Fin m) (P p : Fin m) (x : Fin n)
    (hM : FirstOrder.Theory.Models M nativeZF) :
    (Translation.sentence (formulaBridgeSentence L H lp v P p x)).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro env hpre hp
  have hpre' := (ForcingAtomicBasic.preorder_semantics (M := M) env L lp P).mp hpre
  refine ⟨?_,?_⟩
  · have hf := ForcingFormula.formula_semantics (M := M) env L H lp v P p (Source.SetLanguage.transitiveSet x)
    have ht := transF_semantics (M := M) env L H lp P p (v x)
    have hm := forces_transitiveSet hM (H := H) hpre' hp (fun i => env (v i)) x
    exact ⟨fun h => ht.mpr (hm.mp (hf.mp h)),fun h => hf.mpr (hm.mpr (ht.mp h))⟩
  · intro ho
    exact (ordF_semantics (M := M) env L H lp P p (v x)).mpr
      (ordF_of_forces_ordinal hM hpre' hp (fun i => env (v i)) x
        ((ForcingFormula.formula_semantics (M := M) env L H lp v P p (Source.SetLanguage.ordinal x)).mp ho))

theorem formula_bridge_kernel_certificate {k n m : Nat} (L : Formula (k+2)) (H : Formula (k+1))
    (lp : Fin k → Fin m) (v : Fin n → Fin m) (P p : Fin m) (x : Fin n) :
    FirstOrder.Derives nativeZF [] (Translation.sentence (formulaBridgeSentence L H lp v P p x)) :=
  ModelTransfer.derives (fun _ hM => formula_bridge_models L H lp v P p x hM)

end PPAC.Migration.ForcingOrdinalTransitivity
