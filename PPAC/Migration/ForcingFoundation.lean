/- Pinned SymmetricNames.minimal_member -> forces_foundation.
The source Child descent is instantiated by a pure object formula in the
already proved internal name induction. No external WellFounded assumption. -/
import PPAC.Migration.ForcingBasicSetAxioms

namespace PPAC.Migration.ForcingFoundation
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open Source (Formula)
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open ForcingMapConditions (MapRel)
open ForcingAtomicRelations (Forces forces)
open ForcingAtomicBasic (PreorderOn)
open ForcingFormula (Force)
open ForcingClassEvaluation (Predicate)
open ReplacementPredicates (paramsUp rel)
open MinimalPredicates (pred)
open ForcingProductSymmetry (orderFormula)
open ForcingPairUnion (domain domain_semantics)
attribute [local implicit_reducible] SetTheory.signature Definitional.Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def minimal {n m : Nat} (R : Formula (n+2)) (H : Formula (n+1))
    (rho : Fin n → Fin m) (P sigma tau q : Fin m) : Formula m :=
  .all ((pred H (paramsUp rho) (Fin.last m)).imp
    (.all ((Formula.mem (Fin.last (m+1)) P.castSucc.castSucc).imp
      ((rel R (paramsUp (paramsUp rho)) (Fin.last (m+1)) q.castSucc.castSucc).imp
        ((forces false R (paramsUp (paramsUp rho)) P.castSucc.castSucc
          (Fin.last m).castSucc tau.castSucc.castSucc (Fin.last (m+1))).imp
          (forces false R (paramsUp (paramsUp rho)) P.castSucc.castSucc
            (Fin.last m).castSucc sigma.castSucc.castSucc (Fin.last (m+1))).neg)))))

def Minimal {n : Nat} (R : Formula (n+2)) (H : Formula (n+1))
    (env : Fin n → M.Carrier .set) (P sigma tau q : M.Carrier .set) : Prop :=
  ∀ nu, Predicate H env nu → ∀ r,
    (Definitional.Project.FirstOrderSemantics.reduct M).mem r P → MapRel R env r q →
    Forces false R env P nu tau r → ¬Forces false R env P nu sigma r

theorem minimal_semantics {n m : Nat} (v : Fin m → M.Carrier .set)
    (R : Formula (n+2)) (H : Formula (n+1)) (rho : Fin n → Fin m) (P sigma tau q : Fin m) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem v (minimal R H rho P sigma tau q) ↔
      Minimal R H (fun i => v (rho i)) (v P) (v sigma) (v tau) (v q) := by
  simp only [minimal,Minimal,Formula.Realize,ForcingNameInduction.pred_semantics,
    ForcingMapConditions.rel_semantics (M := M),ForcingAtomicRelations.forces_semantics (M := M),
    paramsUp,Fin.lastCases_last,Fin.lastCases_castSucc]
  rfl

def witness {n m : Nat} (R : Formula (n+2)) (H : Formula (n+1))
    (rho : Fin n → Fin m) (P sigma p : Fin m) : Formula m :=
  .ex ((Formula.mem (Fin.last m) P.castSucc).conj
    ((rel R (paramsUp rho) (Fin.last m) p.castSucc).conj
      (.ex ((pred H (paramsUp (paramsUp rho)) (Fin.last (m+1))).conj
        ((forces false R (paramsUp (paramsUp rho)) P.castSucc.castSucc
          (Fin.last (m+1)) sigma.castSucc.castSucc (Fin.last m).castSucc).conj
          (minimal R H (paramsUp (paramsUp rho)) P.castSucc.castSucc
            sigma.castSucc.castSucc (Fin.last (m+1)) (Fin.last m).castSucc))))))

def Witness {n : Nat} (R : Formula (n+2)) (H : Formula (n+1))
    (env : Fin n → M.Carrier .set) (P sigma p : M.Carrier .set) : Prop :=
  ∃ q, (Definitional.Project.FirstOrderSemantics.reduct M).mem q P ∧ MapRel R env q p ∧
    ∃ tau, Predicate H env tau ∧ Forces false R env P tau sigma q ∧ Minimal R H env P sigma tau q

theorem witness_semantics {n m : Nat} (v : Fin m → M.Carrier .set)
    (R : Formula (n+2)) (H : Formula (n+1)) (rho : Fin n → Fin m) (P sigma p : Fin m) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem v (witness R H rho P sigma p) ↔
      Witness R H (fun i => v (rho i)) (v P) (v sigma) (v p) := by
  simp only [witness,Witness,Formula.Realize,ForcingNameInduction.pred_semantics,
    ForcingMapConditions.rel_semantics (M := M),ForcingAtomicRelations.forces_semantics (M := M),
    minimal_semantics (M := M),paramsUp,Fin.lastCases_last,Fin.lastCases_castSucc]
  rfl

def inductionPredicate {n m : Nat} (R : Formula (n+2)) (H : Formula (n+1))
    (rho : Fin n → Fin m) (P sigma nu : Fin m) : Formula m :=
  (pred H rho nu).imp (.all
    ((forces false R (paramsUp rho) P.castSucc nu.castSucc sigma.castSucc (Fin.last m)).imp
      (witness R H (paramsUp rho) P.castSucc sigma.castSucc (Fin.last m))))

theorem inductionPredicate_semantics {n m : Nat} (v : Fin m → M.Carrier .set)
    (R : Formula (n+2)) (H : Formula (n+1)) (rho : Fin n → Fin m) (P sigma nu : Fin m) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem v
      (inductionPredicate R H rho P sigma nu) ↔
    (Predicate H (fun i => v (rho i)) (v nu) → ∀ p,
      Forces false R (fun i => v (rho i)) (v P) (v nu) (v sigma) p →
      Witness R H (fun i => v (rho i)) (v P) (v sigma) p) := by
  simp only [inductionPredicate,Formula.Realize,ForcingNameInduction.pred_semantics,
    ForcingAtomicRelations.forces_semantics (M := M),witness_semantics (M := M),
    paramsUp,Fin.lastCases_last,Fin.lastCases_castSucc]
  rfl

theorem minimal_member (hM : FirstOrder.Theory.Models M nativeZF) {n : Nat}
    (R : Formula (n+2)) (H : Formula (n+1)) (env : Fin n → M.Carrier .set)
    (P sigma : M.Carrier .set) (hpre : PreorderOn R env P)
    (hchild : ∀ nu, Predicate H env nu → ∀ chi c, PureKuratowski.PairMember M chi c nu → Predicate H env chi)
    (nu p : M.Carrier .set) (hnu : Predicate H env nu) (hmem : Forces false R env P nu sigma p) :
    Witness R H env P sigma p := by
  classical
  let matrix := inductionPredicate R H (fun i => i.castSucc.castSucc.castSucc)
    (Fin.last n).castSucc.castSucc (Fin.last (n+1)).castSucc (Fin.last (n+2))
  let inputs : Fin (n+2) → M.Carrier .set := Fin.lastCases sigma (Fin.lastCases P env)
  have hm : ∀ x, Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem
      (Fin.lastCases x inputs) matrix ↔
      (Predicate H env x → ∀ p, Forces false R env P x sigma p → Witness R H env P sigma p) := by
    intro x
    simpa only [inputs,Fin.lastCases_last,Fin.lastCases_castSucc] using
      (inductionPredicate_semantics (M := M) (Fin.lastCases x inputs) R H
        (fun i => i.castSucc.castSucc.castSucc) (Fin.last n).castSucc.castSucc
        (Fin.last (n+1)).castSucc (Fin.last (n+2)))
  have hall := ForcingMapLaws.formula_induction hM matrix inputs (by
    intro x ih
    apply (hm x).mpr
    intro hx p hpMem
    have hp := ForcingAtomicBasic.condition hM hpMem
    by_cases hn : ∃ q, (Definitional.Project.FirstOrderSemantics.reduct M).mem q P ∧ MapRel R env q p ∧
        ∃ y, Predicate H env y ∧ Forces false R env P y x q ∧ Forces false R env P y sigma q
    · obtain ⟨q,hq,hqp,y,hy,hyx,hys⟩ := hn
      obtain ⟨r,chi,c,hr,hrq,hc,he,hrc,heq⟩ :=
        ((ForcingAtomicRelations.mem_iff hM R env P y x q).mp hyx).2 q hq (hpre.1 q hq)
      have hchi := (ForcingAtomicLaws.mem_congr_left hM hpre heq).mp
        (ForcingAtomicBasic.mem_mono hM hpre hr hrq hys)
      obtain ⟨s,hs,hsr,tau,ht,hmem,hmin⟩ :=
        (hm chi).mp (ih chi c he) (hchild x hx chi c he) r hchi
      exact ⟨s,hs,hpre.2 s q p hs hq hp (hpre.2 s r q hs hr hq hsr hrq) hqp,tau,ht,hmem,hmin⟩
    · refine ⟨p,hp,hpre.1 p hp,x,hx,hpMem,?_⟩
      intro y hy r hr hrp hyx hys
      exact hn ⟨r,hr,hrp,y,hy,hyx,hys⟩)
  exact (hm nu).mp (hall nu) hnu p hmem

theorem forces_foundation (hM : FirstOrder.Theory.Models M nativeZF) {n : Nat}
    (env : Fin n → M.Carrier .set) (rho : Fin 7 → Fin n) (G F mul : Fin n)
    {p : M.Carrier .set}
    (hpre : PreorderOn (orderFormula (rho 0) mul) env (env (rho 6)))
    (hp : (Definitional.Project.FirstOrderSemantics.reduct M).mem p (env (rho 6))) :
    Force (orderFormula (rho 0) mul) (domain rho G F) env Fin.elim0 (env (rho 6)) p Source.SetLanguage.foundation := by
  let R := orderFormula (rho 0) mul
  let H := domain rho G F
  let W := env (rho 6)
  have hchild : ∀ nu, Predicate H env nu → ∀ chi c,
      PureKuratowski.PairMember M chi c nu → Predicate H env chi := by
    intro nu hnu chi c he
    exact (domain_semantics env rho G F chi).mpr
      (ForcingHS.child ((domain_semantics env rho G F nu).mp hnu) he)
  unfold Source.SetLanguage.foundation
  apply (ForcingFormula.force_all hM hpre hp _ _).mpr
  intro sigma hs
  apply (ForcingFormula.force_imp hM hpre hp _ _ _).mpr
  intro q hq hqp hnonempty
  change Force R H env (Fin.lastCases sigma Fin.elim0) W q (.ex (.mem 1 0)) at hnonempty
  apply (ForcingFormula.force_ex R H env _ W q _).mpr
  intro r hr hrq
  obtain ⟨s,hsc,hsr,nu,hnu,hm⟩ := (ForcingFormula.force_ex R H env _ W q _).mp hnonempty r hr hrq
  obtain ⟨t,htc,hts,tau,htau,hmem,hmin⟩ := minimal_member hM R H env W sigma hpre hchild nu s hnu hm
  refine ⟨t,htc,hpre.2 t s r htc hsc hr hts hsr,tau,htau,hmem,?_⟩
  apply (ForcingFormula.force_all hM hpre htc _ _).mpr
  intro nu hnu
  apply (ForcingFormula.force_imp hM hpre htc _ _ _).mpr
  intro a ha hat hnt
  apply (ForcingFormula.force_neg hM hpre ha _ _).mpr
  intro b hb hba hns
  exact hmin nu hnu b hb (hpre.2 b a t hb ha htc hba hat)
    (ForcingAtomicBasic.mem_mono hM hpre hb hba hnt) hns

def sentence : Source.Sentence :=
  let rho : Fin 7 → Fin 16 := fun i => ⟨i.val, Nat.lt_trans i.isLt (by decide)⟩
  let R := orderFormula (0 : Fin 16) 13
  let H := domain rho 11 12
  ((ForcingDiagramPoset.leftCancelMonoid (0 : Fin 16) 13 14).imp
    ((ForcingProductFamily.presentation (0 : Fin 16) 7 8 9 10 1 2 3 4 5 6).imp
      ((Formula.mem (15 : Fin 16) 6).imp
        (ForcingFormula.formula R H id Fin.elim0 6 15 Source.SetLanguage.foundation)))).close

theorem models (hM : FirstOrder.Theory.Models M nativeZF) : (Translation.sentence sentence).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro env hm hp hc
  let rho : Fin 7 → Fin 16 := fun i => ⟨i.val, Nat.lt_trans i.isLt (by decide)⟩
  let R := orderFormula (0 : Fin 16) 13
  let H := domain rho 11 12
  have hm' := (ForcingDiagramPoset.leftCancelMonoid_semantics (M := M) env 0 13 14).mp hm
  have hp' := (ForcingProductFamily.presentation_semantics (M := M) env 0 7 8 9 10 1 2 3 4 5 6).mp hp
  have hpre := ForcingProductPoset.preorder env 0 13 6 hm' hp'.2.2.2.2.1 hp'.2.2.2.1 hp'.2.2.2.2.2
  apply (ForcingFormula.formula_semantics (M := M) env R H id Fin.elim0 6 15 Source.SetLanguage.foundation).mpr
  have hzero : (fun i : Fin 0 => env (Fin.elim0 i)) = (Fin.elim0 : Fin 0 → M.Carrier .set) :=
    funext (fun i => Fin.elim0 i)
  rw [hzero]
  exact forces_foundation hM env rho 11 12 13 hpre hc

theorem kernel_certificate : FirstOrder.Derives nativeZF [] (Translation.sentence sentence) :=
  ModelTransfer.derives (fun _ hM => models hM)

end PPAC.Migration.ForcingFoundation
