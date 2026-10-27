/- Pinned MergerWords.Word.leading/old_dvd_iff:239-271,
old_common_multiple_iff:273, preserve_old_cone_intersection:283,
dvd_snoc_iff:290 and snoc_dvd_snoc_iff:323.
Use the existing Raw coefficient and append representation, not a new parser.
Consumer: Word.exists_cone_join and original Merger old-conservativity. -/
import PPAC.Migration.ConstructionMergerCopyCones

namespace PPAC.Migration.ConstructionMergerWordDivisibility
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionProbeRaw (Raw Carrier Old Cons)
open ConstructionProbeLetters (Representatives)
open ConstructionProbeAction (projected projected_range)
open ConstructionMergerWordAction (ActionTable)
open ConstructionMergerWordProduct (Laws)
open ConstructionMergerCopyCones (Reaches)
open ConstructionBaseMonoid (Divides)
open ConstructionProbeCones (JoinProperty)
open ForcingDiagramOrder (Product product product_semantics)
open ForcingSupportSize (MapsTo)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def Leading (D q x : M.Carrier .set) : Prop :=
  (Project.FirstOrderSemantics.reduct M).mem x D ∧ ∃ f, PureKuratowski.Code M q f x

theorem exists_leading {w D L q : M.Carrier .set} (hq : Raw w D L q) : ∃ x, Leading D q x := by
  obtain ⟨f,x,_,hx,hcode⟩ := hq
  exact ⟨x,hx,f,hcode⟩

theorem leading_unique {D q x y : M.Carrier .set} (hx : Leading D q x) (hy : Leading D q y) : x = y := by
  obtain ⟨_,f,hf⟩ := hx
  obtain ⟨_,g,hg⟩ := hy
  exact (PureKuratowski.code_injective hf hg).2

theorem leading_old {D zero q x : M.Carrier .set} (hq : Old zero D x q) : Leading D q x :=
  ⟨hq.1,zero,hq.2⟩

theorem leading_snoc {w D L s t q x : M.Carrier .set} (hq : Cons w D L s t q) :
    Leading D t x ↔ Leading D q x := by
  obtain ⟨_,_,f,g,y,_,_,_,_,_,hy,_,ht,hq,_⟩ := hq
  constructor
  · intro hx
    have he := leading_unique hx ⟨hy,f,ht⟩
    exact he.symm ▸ (show Leading D q y from ⟨hy,g,hq⟩)
  · intro hx
    have he := leading_unique hx ⟨hy,g,hq⟩
    exact he.symm ▸ (show Leading D t y from ⟨hy,f,ht⟩)

theorem dvd_snoc_iff (hM : FirstOrder.Theory.Models M nativeZF)
    {w D L zero mul A W T H x pref d out : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ p, ¬ (Project.FirstOrderSemantics.reduct M).mem p zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hW : Carrier w D L W) (hTable : ActionTable w D L zero mul A T)
    (hLaws : Laws w D L zero T H) (hCons : Cons w D L d pref out) :
    Divides W H x out ↔ Divides W H x pref ∨ ∃ z, Cons w D L z pref x ∧ Reaches D A z d := by
  constructor
  · rintro ⟨q,hq,hprod⟩
    rcases ConstructionProbeRaw.cases_raw hM hw hz hzw ((hW q).mp hq) with ⟨m,hOld⟩ | ⟨s,t,hSnoc⟩
    · have hAct := (hTable x m out).mp ((hLaws.1 m x q out hOld).mp hprod)
      rcases hAct.2 with ⟨a,am,_,_,hOldOut⟩ | ⟨z,v,zm,hSnocX,hZm,hSnocOut⟩
      · exact (ConstructionProbeRaw.old_ne_cons hz hOldOut hCons).elim
      · obtain ⟨rfl,rfl⟩ := ConstructionProbeRaw.cons_injective hM hw hSnocOut hCons
        exact Or.inr ⟨z,hSnocX,m,hAct.1,hZm⟩
    · obtain ⟨v,hv,hSnocOut⟩ := (hLaws.2 s t q x out hSnoc).mp hprod
      obtain ⟨rfl,rfl⟩ := ConstructionProbeRaw.cons_injective hM hw hSnocOut hCons
      exact Or.inl ⟨t,(hW t).mpr (ConstructionProbeRaw.cons_raw hSnoc).1,hv⟩
  · rintro (⟨q,hq,hprod⟩ | ⟨z,hSnocX,m,hm,hZm⟩)
    · have hd : (Project.FirstOrderSemantics.reduct M).mem d L := by
        obtain ⟨_,_,_,_,_,_,_,_,_,_,_,hd,_,_,_⟩ := hCons
        exact hd
      obtain ⟨snocq,hSnocQ⟩ := ConstructionProbeRaw.exists_cons hM hw hd ((hW q).mp hq)
      exact ⟨snocq,(hW snocq).mpr (ConstructionProbeRaw.cons_raw hSnocQ).2,
        (hLaws.2 d q snocq x out hSnocQ).mpr ⟨pref,hprod,hCons⟩⟩
    · obtain ⟨oldm,hOldM⟩ := ConstructionProbeRaw.exists_old hM (zero := zero) hm
      exact ⟨oldm,(hW oldm).mpr (ConstructionProbeRaw.old_raw hM hz hzw hOldM),
        (hLaws.1 m x oldm out hOldM).mpr ((hTable x m out).mpr ⟨hm,Or.inr ⟨z,pref,d,hSnocX,hZm,hCons⟩⟩)⟩

def leading {m0 : Nat} (D q x : Fin m0) : Project.Formula 1 m0 :=
  .conj (.mem (.bound x) (.bound D)) (.existsE (PureKuratowskiProject.code (.bound q.succ) (.bound 0) (.bound x.succ)))

theorem leading_freeClosed {m0 : Nat} (D q x : Fin m0) : (leading D q x).FreeClosed := by
  simp -implicitDefEqProofs [leading,Definitional.Formula.FreeClosed,PureKuratowskiProject.code]

theorem leading_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m0 : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m0) (D q x : Fin m0) :
    Project.Formula.satisfies env (leading D q x) ↔ Leading (env.bound D) (env.bound q) (env.bound x) := by
  simp only [leading,Leading,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,KuratowskiZF.code_correct hM]
  rfl

def oldDivAt {m0 : Nat} (D zero mul W H q : Fin m0) : Project.Formula 1 m0 :=
  (.forallE (.forallE (.forallE (.imp (ConstructionProbeRaw.old zero.succ.succ.succ D.succ.succ.succ 2 1) (.imp (leading D.succ.succ.succ q.succ.succ.succ 0) (.iff (ProjectSyntax.encode id (ConstructionBaseMonoid.divides W.succ.succ.succ H.succ.succ.succ 1 q.succ.succ.succ)) (ProjectSyntax.encode id (ConstructionBaseMonoid.divides D.succ.succ.succ mul.succ.succ.succ 2 0))))))))

theorem oldDivAt_freeClosed {m0 : Nat} (D zero mul W H q : Fin m0) : (oldDivAt D zero mul W H q).FreeClosed := by
  simp -implicitDefEqProofs [oldDivAt,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,ConstructionProbeRaw.old_freeClosed,leading_freeClosed]

theorem oldDivAt_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m0 : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m0) (D zero mul W H q : Fin m0) :
    Project.Formula.satisfies env (oldDivAt D zero mul W H q) ↔ ∀ x ox a,
      Old (env.bound zero) (env.bound D) x ox → Leading (env.bound D) (env.bound q) a →
        (Divides (env.bound W) (env.bound H) ox (env.bound q) ↔ Divides (env.bound D) (env.bound mul) x a) := by
  simp only [oldDivAt,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_iff_iff,ConstructionProbeRaw.old_semantics hM,leading_semantics hM,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ConstructionBaseMonoid.divides_semantics (M := M)]
  rfl

theorem old_dvd_iff (hM : FirstOrder.Theory.Models M nativeZF)
    {w D L zero mul A W B H T q x ox a : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ p, ¬ (Project.FirstOrderSemantics.reduct M).mem p zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hW : Carrier w D L W) (hB : Representatives W W B) (hH : MapsTo B W H)
    (hTable : ActionTable w D L zero mul A T) (hLaws : Laws w D L zero T H)
    (hq : Raw w D L q) (hOldX : Old zero D x ox) (hLead : Leading D q a) :
    Divides W H ox q ↔ Divides D mul x a := by
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 5 := {
    bound := fun i => match i with | 0 => D | 1 => zero | 2 => mul | 3 => W | _ => H,
    free := fun _ => w }
  let p : Project.UnarySchema 5 := { body := oldDivAt 1 2 3 4 5 0,freeClosed := oldDivAt_freeClosed _ _ _ _ _ _ }
  have he (b) : p.denote env b ↔ ∀ y oy c, Old zero D y oy → Leading D b c →
      (Divides W H oy b ↔ Divides D mul y c) := oldDivAt_semantics hM (env.push b) 1 2 3 4 5 0
  have hAll := ConstructionProbeEvaluationLaws.raw_induction hM env p hw hz hzw (by
    intro m b hOld
    apply (he b).mpr
    intro y oy c hY hC
    have hcEq := leading_unique hC (leading_old hOld)
    subst c
    constructor
    · rintro ⟨r,hr,hprod⟩
      obtain ⟨y',r',hY',hR',hmul⟩ := ConstructionMergerWordMonoid.factors_of_old hM hw hz hzw hW hB hH hTable hLaws hOld hprod
      have hyEq := ConstructionProbeRaw.old_injective hY' hY
      exact ⟨r',hR'.1,hyEq ▸ hmul⟩
    · rintro ⟨r,hr,hmul⟩
      obtain ⟨orr,hR⟩ := ConstructionProbeRaw.exists_old hM (zero := zero) hr
      exact ⟨orr,(hW orr).mpr (ConstructionProbeRaw.old_raw hM hz hzw hR),
        (hLaws.1 r oy orr b hR).mpr ((hTable oy r b).mpr ⟨hr,Or.inl ⟨y,m,hY,hmul,hOld⟩⟩)⟩) (by
    intro s t b hCons ih
    apply (he b).mpr
    intro y oy c hY hC
    have hCt := (leading_snoc hCons).mpr hC
    have hI := (he t).mp ih y oy c hY hCt
    refine (dvd_snoc_iff hM hw hz hzw hW hTable hLaws hCons).trans ?_
    constructor
    · rintro (ht | ⟨z,hSnoc,_⟩)
      · exact hI.mp ht
      · exact (ConstructionProbeRaw.old_ne_cons hz hY hSnoc).elim
    · intro h
      exact Or.inl (hI.mpr h))
  exact (he q).mp (hAll q hq) x ox a hOldX hLead

theorem preserve_old_cone_intersection (hM : FirstOrder.Theory.Models M nativeZF)
    {w D L zero mul A W B H T x y j ox oy oj : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ p, ¬ (Project.FirstOrderSemantics.reduct M).mem p zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hW : Carrier w D L W) (hB : Representatives W W B) (hH : MapsTo B W H)
    (hTable : ActionTable w D L zero mul A T) (hLaws : Laws w D L zero T H)
    (hX : Old zero D x ox) (hY : Old zero D y oy) (hJ : Old zero D j oj)
    (hJoin : JoinProperty D mul x y j) : JoinProperty W H ox oy oj := by
  intro b hb
  have hbRaw := (hW b).mp hb
  obtain ⟨a,ha⟩ := exists_leading hbRaw
  have hx := old_dvd_iff hM hw hz hzw hW hB hH hTable hLaws hbRaw hX ha
  have hy := old_dvd_iff hM hw hz hzw hW hB hH hTable hLaws hbRaw hY ha
  have hj := old_dvd_iff hM hw hz hzw hW hB hH hTable hLaws hbRaw hJ ha
  rw [hx,hy,hj]
  exact hJoin a ha.1

theorem old_common_multiple_iff (hM : FirstOrder.Theory.Models M nativeZF)
    {w D L zero mul A W B H T x y ox oy : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ p, ¬ (Project.FirstOrderSemantics.reduct M).mem p zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hW : Carrier w D L W) (hB : Representatives W W B) (hH : MapsTo B W H)
    (hTable : ActionTable w D L zero mul A T) (hLaws : Laws w D L zero T H)
    (hX : Old zero D x ox) (hY : Old zero D y oy) :
    (∃ b, (Project.FirstOrderSemantics.reduct M).mem b W ∧ Divides W H ox b ∧ Divides W H oy b) ↔
      ∃ a, (Project.FirstOrderSemantics.reduct M).mem a D ∧ Divides D mul x a ∧ Divides D mul y a := by
  constructor
  · rintro ⟨b,hb,hxb,hyb⟩
    have hbRaw := (hW b).mp hb
    obtain ⟨a,ha⟩ := exists_leading hbRaw
    exact ⟨a,ha.1,(old_dvd_iff hM hw hz hzw hW hB hH hTable hLaws hbRaw hX ha).mp hxb,
      (old_dvd_iff hM hw hz hzw hW hB hH hTable hLaws hbRaw hY ha).mp hyb⟩
  · rintro ⟨a,ha,hxa,hya⟩
    obtain ⟨oa,hA⟩ := ConstructionProbeRaw.exists_old hM (zero := zero) ha
    have hRaw : Raw w D L oa := ConstructionProbeRaw.old_raw hM hz hzw hA
    exact ⟨oa,(hW oa).mpr hRaw,(old_dvd_iff hM hw hz hzw hW hB hH hTable hLaws hRaw hX (leading_old hA)).mpr hxa,
      (old_dvd_iff hM hw hz hzw hW hB hH hTable hLaws hRaw hY (leading_old hA)).mpr hya⟩

theorem snoc_dvd_snoc_iff (hM : FirstOrder.Theory.Models M nativeZF)
    {w D L zero mul A W T H z pref x d pref' out : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ p, ¬ (Project.FirstOrderSemantics.reduct M).mem p zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hW : Carrier w D L W) (hTable : ActionTable w D L zero mul A T)
    (hLaws : Laws w D L zero T H) (hX : Cons w D L z pref x) (hOut : Cons w D L d pref' out) :
    Divides W H x out ↔ Divides W H x pref' ∨ (pref = pref' ∧ Reaches D A z d) := by
  refine (dvd_snoc_iff hM hw hz hzw hW hTable hLaws hOut).trans ?_
  constructor
  · rintro (h | ⟨s,hS,hReach⟩)
    · exact Or.inl h
    · obtain ⟨rfl,rfl⟩ := ConstructionProbeRaw.cons_injective hM hw hX hS
      exact Or.inr ⟨rfl,hReach⟩
  · rintro (h | ⟨rfl,hReach⟩)
    · exact Or.inl h
    · exact Or.inr ⟨z,hX,hReach⟩

end PPAC.Migration.ConstructionMergerWordDivisibility
