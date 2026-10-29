/- Pinned ProductNames.eq_check_iff/mem_check_check, consumed by
PersistentCodes.ordF_eq_check_le. Internal member induction replaces only
the source host well-founded induction; actual check names are unchanged. -/
import PPAC.Migration.ForcingInfinity

namespace PPAC.Migration.ForcingCheckReflection
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open Source (Formula)
open ReplacementPredicates (paramsUp rel)
open ForcingMapConditions (MapRel)
open ForcingAtomicRelations (Forces forces)
open ForcingAtomicBasic (PreorderOn)
open ForcingCheckName (Checked checkName)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def equalityAt {k m : Nat} (L : Formula (k+2)) (lp : Fin k → Fin m) (P top x : Fin m) : Formula m :=
  let up : Fin m → Fin (m+4) := fun i => i.castSucc.castSucc.castSucc.castSucc
  let y := (Fin.last m).castSucc.castSucc.castSucc
  let nx := (Fin.last (m+1)).castSucc.castSucc
  let ny := (Fin.last (m+2)).castSucc
  let p := Fin.last (m+3)
  .all (.all (.all (.all ((checkName (up top) (up x) nx).imp
    ((checkName (up top) y ny).imp ((forces true L (fun i => up (lp i)) (up P) nx ny p).imp
      (.equal (up x) y)))))))

theorem equalityAt_semantics {k m : Nat} (env : Fin m → M.Carrier .set)
    (L : Formula (k+2)) (lp : Fin k → Fin m) (P top x : Fin m) :
    Formula.Realize (Project.FirstOrderSemantics.reduct M).mem env (equalityAt L lp P top x) ↔
      ∀ y nx ny p, Checked (env top) (env x) nx → Checked (env top) y ny →
        Forces true L (fun i => env (lp i)) (env P) nx ny p → env x = y := by
  simp only [equalityAt,Formula.Realize,ForcingCheckName.checkName_semantics (M := M),
    ForcingAtomicRelations.forces_semantics (M := M),Fin.lastCases_last,Fin.lastCases_castSucc]
  rfl

theorem equality_reflects (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    {L : Formula (k+2)} {lp : Fin k → M.Carrier .set} {P top : M.Carrier .set}
    (hpre : PreorderOn L lp P) (ht : (Project.FirstOrderSemantics.reduct M).mem top P)
    (htop : ∀ q, (Project.FirstOrderSemantics.reduct M).mem q P → MapRel L lp q top) :
    ∀ x y nx ny p, Checked top x nx → Checked top y ny → Forces true L lp P nx ny p → x = y := by
  let inputs : Fin (k+2) → M.Carrier .set := Fin.lastCases top (Fin.lastCases P lp)
  let matrix := equalityAt L (fun i => i.castSucc.castSucc.castSucc)
    (Fin.last k).castSucc.castSucc (Fin.last (k+1)).castSucc (Fin.last (k+2))
  have hm : ∀ x, Formula.Realize (Project.FirstOrderSemantics.reduct M).mem (Fin.lastCases x inputs) matrix ↔
      ∀ y nx ny p, Checked top x nx → Checked top y ny → Forces true L lp P nx ny p → x = y := by
    intro x
    simpa only [inputs,Fin.lastCases_last,Fin.lastCases_castSucc] using
      equalityAt_semantics (M := M) (Fin.lastCases x inputs) L (fun i => i.castSucc.castSucc.castSucc)
        (Fin.last k).castSucc.castSucc (Fin.last (k+1)).castSucc (Fin.last (k+2))
  have all := ForcingCheckName.formula_induction hM matrix inputs (by
    intro x ih
    apply (hm x).mpr
    intro y nx ny p hx hy he
    have hp := ForcingAtomicBasic.condition hM he
    apply (ModelTransfer.extensionality hM).eq_of_same_members
    intro z
    obtain ⟨nz,hz⟩ := ForcingCheckName.exists_checked hM top z
    constructor
    · intro hzx
      have hzy := (ForcingAtomicLaws.mem_congr_right hM hpre he).mp
        (ForcingInfinity.check_mem_of_mem hM hpre hx hz hzx ht htop hp)
      obtain ⟨r,_,_,a,hay,na,ha,hea⟩ := (ForcingInfinity.mem_check hM hy ht htop hp).mp hzy p hp (hpre.1 p hp)
      have hza := (hm z).mp (ih z hzx) a nz na r hz ha hea
      exact hza.symm ▸ hay
    · intro hzy
      have hzx := (ForcingAtomicLaws.mem_congr_right hM hpre he).mpr
        (ForcingInfinity.check_mem_of_mem hM hpre hy hz hzy ht htop hp)
      obtain ⟨r,_,_,a,hax,na,ha,hea⟩ := (ForcingInfinity.mem_check hM hx ht htop hp).mp hzx p hp (hpre.1 p hp)
      have haz := (hm a).mp (ih a hax) z na nz r ha hz (ForcingAtomicBasic.eq_symm hM hea)
      exact haz ▸ hax)
  intro x
  exact (hm x).mp (all x)

theorem eq_check_iff (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    {L : Formula (k+2)} {lp : Fin k → M.Carrier .set} {P top x y nx ny p : M.Carrier .set}
    (hpre : PreorderOn L lp P) (ht : (Project.FirstOrderSemantics.reduct M).mem top P)
    (htop : ∀ q, (Project.FirstOrderSemantics.reduct M).mem q P → MapRel L lp q top)
    (hp : (Project.FirstOrderSemantics.reduct M).mem p P) (hx : Checked top x nx) (hy : Checked top y ny) :
    Forces true L lp P nx ny p ↔ x = y := by
  refine ⟨equality_reflects hM hpre ht htop x y nx ny p hx hy,?_⟩
  intro he
  subst y
  have hn := ForcingCheckName.unique hM hx hy
  exact hn ▸ ForcingAtomicBasic.eq_refl hM hpre nx p hp

theorem mem_check_check (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    {L : Formula (k+2)} {lp : Fin k → M.Carrier .set} {P top x y nx ny p : M.Carrier .set}
    (hpre : PreorderOn L lp P) (ht : (Project.FirstOrderSemantics.reduct M).mem top P)
    (htop : ∀ q, (Project.FirstOrderSemantics.reduct M).mem q P → MapRel L lp q top)
    (hp : (Project.FirstOrderSemantics.reduct M).mem p P) (hx : Checked top x nx) (hy : Checked top y ny) :
    Forces false L lp P nx ny p ↔ (Project.FirstOrderSemantics.reduct M).mem x y := by
  refine ⟨?_,fun hm => ForcingInfinity.check_mem_of_mem hM hpre hy hx hm ht htop hp⟩
  intro hm
  obtain ⟨r,hr,_,z,hz,nz,hnz,he⟩ := (ForcingInfinity.mem_check hM hy ht htop hp).mp hm p hp (hpre.1 p hp)
  have hxz := (eq_check_iff hM hpre ht htop hr hx hnz).mp he
  exact hxz.symm ▸ hz

def comparisonSentence {k m : Nat} (L : Formula (k+2)) (lp : Fin k → Fin m)
    (P top x y nx ny p : Fin m) : Source.Sentence :=
  ((ForcingAtomicBasic.preorder L lp P).imp ((Formula.mem top P).imp
    ((Formula.all ((Formula.mem (Fin.last m) P.castSucc).imp
      (rel L (paramsUp lp) (Fin.last m) top.castSucc))).imp
      ((Formula.mem p P).imp ((checkName top x nx).imp ((checkName top y ny).imp
        (((forces true L lp P nx ny p).iff (.equal x y)).conj
          ((forces false L lp P nx ny p).iff (.mem x y))))))))).close

theorem comparison_models {k m : Nat} (L : Formula (k+2)) (lp : Fin k → Fin m)
    (P top x y nx ny p : Fin m) (hM : FirstOrder.Theory.Models M nativeZF) :
    (Translation.sentence (comparisonSentence L lp P top x y nx ny p)).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro env hpre ht htop hp hx hy
  have hpre' := (ForcingAtomicBasic.preorder_semantics (M := M) env L lp P).mp hpre
  have ht' : ∀ q, (Project.FirstOrderSemantics.reduct M).mem q (env P) →
      MapRel L (fun i => env (lp i)) q (env top) := by
    intro q hq
    have hq' : Formula.Realize (Project.FirstOrderSemantics.reduct M).mem (Fin.lastCases q env)
        (.mem (Fin.last m) P.castSucc) := by
      simpa only [Formula.Realize,Fin.lastCases_last,Fin.lastCases_castSucc] using hq
    let vq : Fin (m+1) → M.Carrier .set := Fin.lastCases q env
    have htopq : Formula.Realize (Project.FirstOrderSemantics.reduct M).mem vq
        (rel L (paramsUp lp) (Fin.last m) top.castSucc) := htop q hq'
    have h := (ForcingMapConditions.rel_semantics (M := M) vq L
      (paramsUp lp) (Fin.last m) top.castSucc).mp htopq
    simpa only [vq,paramsUp,Fin.lastCases_last,Fin.lastCases_castSucc] using h
  have hx' := (ForcingCheckName.checkName_semantics (M := M) env top x nx).mp hx
  have hy' := (ForcingCheckName.checkName_semantics (M := M) env top y ny).mp hy
  have he := eq_check_iff hM hpre' ht ht' hp hx' hy'
  have hm := mem_check_check hM hpre' ht ht' hp hx' hy'
  have hfe := ForcingAtomicRelations.forces_semantics (M := M) env true L lp P nx ny p
  have hfm := ForcingAtomicRelations.forces_semantics (M := M) env false L lp P nx ny p
  exact ⟨⟨fun h => he.mp (hfe.mp h),fun h => hfe.mpr (he.mpr h)⟩,
    ⟨fun h => hm.mp (hfm.mp h),fun h => hfm.mpr (hm.mpr h)⟩⟩

theorem comparison_kernel_certificate {k m : Nat} (L : Formula (k+2)) (lp : Fin k → Fin m)
    (P top x y nx ny p : Fin m) : FirstOrder.Derives nativeZF []
      (Translation.sentence (comparisonSentence L lp P top x y nx ny p)) :=
  ModelTransfer.derives (fun _ hM => comparison_models L lp P top x y nx ny p hM)

end PPAC.Migration.ForcingCheckReflection
