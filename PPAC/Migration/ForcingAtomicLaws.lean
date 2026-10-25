/- Pinned AtomicForcing.atomic_laws, eq_trans and mem_congr_left/right.
The three conclusions are proved together with the exact four recursive
queries of the source proof. The source rank/permutation reasoning is consumed
through the existing internal Child-based triple induction, not assumed laws. -/
import PPAC.Migration.ForcingAtomicBasic
import PPAC.Migration.ForcingTripleInduction

namespace PPAC.Migration.ForcingAtomicLaws
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open Source (Formula)
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open ForcingAtomicRelations (Forces forces)
open ForcingAtomicBasic (PreorderOn)
attribute [local implicit_reducible] SetTheory.signature Definitional.Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def laws {n m : Nat} (R : Formula (n+2)) (rho : Fin n → Fin m) (P a b c : Fin m) : Formula m :=
  let r := ReplacementPredicates.paramsUp rho
  let pp := P.castSucc
  let aa := a.castSucc
  let bb := b.castSucc
  let cc := c.castSucc
  let p := Fin.last m
  .all (((forces true R r pp aa bb p).imp ((forces true R r pp bb cc p).imp (forces true R r pp aa cc p))).conj
    (((forces true R r pp aa bb p).imp ((forces false R r pp aa cc p).imp (forces false R r pp bb cc p))).conj
      ((forces true R r pp bb cc p).imp ((forces false R r pp aa bb p).imp (forces false R r pp aa cc p)))))

def Laws {n : Nat} (R : Formula (n+2)) (params : Fin n → M.Carrier .set) (P a b c : M.Carrier .set) : Prop :=
  ∀ p,
    (Forces true R params P a b p → Forces true R params P b c p → Forces true R params P a c p) ∧
    (Forces true R params P a b p → Forces false R params P a c p → Forces false R params P b c p) ∧
    (Forces true R params P b c p → Forces false R params P a b p → Forces false R params P a c p)

theorem laws_semantics {n m : Nat} (v : Fin m → M.Carrier .set) (R : Formula (n+2))
    (rho : Fin n → Fin m) (P a b c : Fin m) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem v (laws R rho P a b c) ↔
      Laws R (fun i => v (rho i)) (v P) (v a) (v b) (v c) := by
  simp only [laws,Laws,Formula.Realize,ForcingAtomicRelations.forces_semantics (M := M),
    ReplacementPredicates.paramsUp,Fin.lastCases_last,Fin.lastCases_castSucc]
  rfl

theorem atomic_laws (hM : FirstOrder.Theory.Models M nativeZF) {n : Nat}
    (R : Formula (n+2)) (params : Fin n → M.Carrier .set) (P : M.Carrier .set)
    (hpre : PreorderOn R params P) : ∀ a b c, Laws R params P a b c := by
  let matrix := laws R (fun i => i.castSucc.castSucc.castSucc.castSucc)
    (Fin.last n).castSucc.castSucc.castSucc (Fin.last (n+1)).castSucc.castSucc
    (Fin.last (n+2)).castSucc (Fin.last (n+3))
  let inputs : Fin (n+1) → M.Carrier .set := Fin.lastCases P params
  have hm : ∀ a b c, ForcingNameRecursion.Step matrix inputs a b c ↔ Laws R params P a b c := by
    intro a b c
    have h := laws_semantics (M := M) (Fin.lastCases c (Fin.lastCases b (Fin.lastCases a inputs))) R
      (fun i => i.castSucc.castSucc.castSucc.castSucc) (Fin.last n).castSucc.castSucc.castSucc
      (Fin.last (n+1)).castSucc.castSucc (Fin.last (n+2)).castSucc (Fin.last (n+3))
    simpa only [ForcingNameRecursion.Step,inputs,Fin.lastCases_last,Fin.lastCases_castSucc] using h
  have all := ForcingTripleInduction.formula_induction hM matrix inputs (by
    intro a b c il isw im ir
    apply (hm a b c).mpr
    intro p
    refine ⟨?_,?_,?_⟩
    · intro hab hbc
      have hp := ForcingAtomicBasic.condition hM hab
      apply (ForcingAtomicRelations.eq_iff hM R params P a c p).mpr
      refine ⟨hp,?_,?_⟩
      · intro nu r hr he q hq hqp hqr
        exact ((hm nu b c).mp (il nu r he) q).2.2
          (ForcingAtomicBasic.eq_mono hM hpre hq hqp hbc)
          (((ForcingAtomicRelations.eq_iff hM R params P a b p).mp hab).2.1 nu r hr he q hq hqp hqr)
      · intro nu r hr he q hq hqp hqr
        exact ((hm nu b a).mp (isw nu r he) q).2.2
          (ForcingAtomicBasic.eq_symm hM (ForcingAtomicBasic.eq_mono hM hpre hq hqp hab))
          (((ForcingAtomicRelations.eq_iff hM R params P b c p).mp hbc).2.2 nu r hr he q hq hqp hqr)
    · intro hab hac
      have hp := ForcingAtomicBasic.condition hM hab
      apply (ForcingAtomicRelations.mem_iff hM R params P b c p).mpr
      refine ⟨hp,?_⟩
      intro q hq hqp
      obtain ⟨s,nu,r,hs,hsq,hr,he,hsr,heq⟩ :=
        ((ForcingAtomicRelations.mem_iff hM R params P a c p).mp hac).2 q hq hqp
      exact ⟨s,nu,r,hs,hsq,hr,he,hsr,((hm b a nu).mp (im nu r he) s).1
        (ForcingAtomicBasic.eq_symm hM (ForcingAtomicBasic.eq_mono hM hpre hs
          (hpre.2 s q p hs hq hp hsq hqp) hab)) heq⟩
    · intro hbc hab
      have hp := ForcingAtomicBasic.condition hM hbc
      apply ForcingAtomicBasic.mem_of_dense hM hpre hp
      intro q hq hqp
      obtain ⟨s,nu,r,hs,hsq,hr,he,hsr,heq⟩ :=
        ((ForcingAtomicRelations.mem_iff hM R params P a b p).mp hab).2 q hq hqp
      exact ⟨s,hs,hsq,((hm nu a c).mp (ir nu r he) s).2.1
        (ForcingAtomicBasic.eq_symm hM heq)
        (((ForcingAtomicRelations.eq_iff hM R params P b c p).mp hbc).2.1 nu r hr he s hs
          (hpre.2 s q p hs hq hp hsq hqp) hsr)⟩)
  intro a b c
  exact (hm a b c).mp (all a b c)

theorem eq_trans (hM : FirstOrder.Theory.Models M nativeZF) {n : Nat}
    {R : Formula (n+2)} {params : Fin n → M.Carrier .set} {P a b c p : M.Carrier .set}
    (hpre : PreorderOn R params P) (hab : Forces true R params P a b p) (hbc : Forces true R params P b c p) :
    Forces true R params P a c p := (atomic_laws hM R params P hpre a b c p).1 hab hbc

theorem mem_congr_left (hM : FirstOrder.Theory.Models M nativeZF) {n : Nat}
    {R : Formula (n+2)} {params : Fin n → M.Carrier .set} {P a b c p : M.Carrier .set}
    (hpre : PreorderOn R params P) (hab : Forces true R params P a b p) :
    Forces false R params P a c p ↔ Forces false R params P b c p :=
  ⟨(atomic_laws hM R params P hpre a b c p).2.1 hab,
    (atomic_laws hM R params P hpre b a c p).2.1 (ForcingAtomicBasic.eq_symm hM hab)⟩

theorem mem_congr_right (hM : FirstOrder.Theory.Models M nativeZF) {n : Nat}
    {R : Formula (n+2)} {params : Fin n → M.Carrier .set} {P a b c p : M.Carrier .set}
    (hpre : PreorderOn R params P) (hbc : Forces true R params P b c p) :
    Forces false R params P a b p ↔ Forces false R params P a c p :=
  ⟨(atomic_laws hM R params P hpre a b c p).2.2 hbc,
    (atomic_laws hM R params P hpre a c b p).2.2 (ForcingAtomicBasic.eq_symm hM hbc)⟩

def lawsSentence {n : Nat} (R : Formula (n+2)) (P a b c : Fin n) : Source.Sentence :=
  ((ForcingAtomicBasic.preorder R id P).imp (laws R id P a b c)).close

def leftSentence {n : Nat} (R : Formula (n+2)) (P a b c p : Fin n) : Source.Sentence :=
  ((ForcingAtomicBasic.preorder R id P).imp ((forces true R id P a b p).imp
    ((forces false R id P a c p).iff (forces false R id P b c p)))).close

def rightSentence {n : Nat} (R : Formula (n+2)) (P a b c p : Fin n) : Source.Sentence :=
  ((ForcingAtomicBasic.preorder R id P).imp ((forces true R id P b c p).imp
    ((forces false R id P a b p).iff (forces false R id P a c p)))).close

theorem laws_models {n : Nat} (R : Formula (n+2)) (P a b c : Fin n)
    (hM : FirstOrder.Theory.Models M nativeZF) : (Translation.sentence (lawsSentence R P a b c)).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro v hpre
  exact (laws_semantics (M := M) v R id P a b c).mpr
    (atomic_laws hM R v (v P) ((ForcingAtomicBasic.preorder_semantics (M := M) v R id P).mp hpre) (v a) (v b) (v c))

theorem left_models {n : Nat} (R : Formula (n+2)) (P a b c p : Fin n)
    (hM : FirstOrder.Theory.Models M nativeZF) : (Translation.sentence (leftSentence R P a b c p)).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro v hpre hab
  have h := (ForcingAtomicRelations.forces_semantics (M := M) v false R id P a c p).trans
    ((mem_congr_left hM ((ForcingAtomicBasic.preorder_semantics (M := M) v R id P).mp hpre)
      ((ForcingAtomicRelations.forces_semantics (M := M) v true R id P a b p).mp hab)).trans
      (ForcingAtomicRelations.forces_semantics (M := M) v false R id P b c p).symm)
  exact ⟨h.mp,h.mpr⟩

theorem right_models {n : Nat} (R : Formula (n+2)) (P a b c p : Fin n)
    (hM : FirstOrder.Theory.Models M nativeZF) : (Translation.sentence (rightSentence R P a b c p)).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro v hpre hbc
  have h := (ForcingAtomicRelations.forces_semantics (M := M) v false R id P a b p).trans
    ((mem_congr_right hM ((ForcingAtomicBasic.preorder_semantics (M := M) v R id P).mp hpre)
      ((ForcingAtomicRelations.forces_semantics (M := M) v true R id P b c p).mp hbc)).trans
      (ForcingAtomicRelations.forces_semantics (M := M) v false R id P a c p).symm)
  exact ⟨h.mp,h.mpr⟩

theorem laws_kernel_certificate {n : Nat} (R : Formula (n+2)) (P a b c : Fin n) :
    FirstOrder.Derives nativeZF [] (Translation.sentence (lawsSentence R P a b c)) :=
  ModelTransfer.derives (fun _ hM => laws_models R P a b c hM)

theorem left_kernel_certificate {n : Nat} (R : Formula (n+2)) (P a b c p : Fin n) :
    FirstOrder.Derives nativeZF [] (Translation.sentence (leftSentence R P a b c p)) :=
  ModelTransfer.derives (fun _ hM => left_models R P a b c p hM)

theorem right_kernel_certificate {n : Nat} (R : Formula (n+2)) (P a b c p : Fin n) :
    FirstOrder.Derives nativeZF [] (Translation.sentence (rightSentence R P a b c p)) :=
  ModelTransfer.derives (fun _ hM => right_models R P a b c p hM)

end PPAC.Migration.ForcingAtomicLaws
