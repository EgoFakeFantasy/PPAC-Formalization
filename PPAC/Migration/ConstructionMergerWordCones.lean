/- Pinned MergerWords.Word.length_le_of_dvd:306,
snoc_not_dvd_prefix/old:311/317, snoc_cone_intersection:338,
exists_cone_join:353. Exact source case split and induction on the common
upper bound. All lengths and induction are internal, including nonstandard.
Consumer: OverlapPrescription.merger_hasConditionalJoins / MergerData.extension. -/
import PPAC.Migration.ConstructionMergerWordDivisibility

namespace PPAC.Migration.ConstructionMergerWordCones
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionProbeRaw (Raw Carrier Old Cons)
open ConstructionProbeLetters (Representatives)
open ConstructionProbeAction (projected projected_range)
open ConstructionMergerWordAction (ActionTable)
open ConstructionMergerWordProduct (Laws)
open ConstructionMergerWordLength (Length exists_length cons_lengths product_length)
open ConstructionMergerWordDivisibility (dvd_snoc_iff snoc_dvd_snoc_iff preserve_old_cone_intersection)
open ConstructionMergerCopyCones (Reaches HasConeJoins)
open ConstructionBaseMonoid (AdditionGraph Divides)
open ConstructionProbeCones (JoinProperty joinProperty joinProperty_freeClosed joinProperty_semantics)
open ConstructionProbeSharedIntersections (ConditionalJoins)
open ConstructionProbeGates (divides_trans)
open ForcingDiagramOrder (Product product product_semantics)
open ForcingDiagramPoset (LeftCancelMonoid)
open ForcingSupportSize (MapsTo)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

theorem length_le_of_dvd (hM : FirstOrder.Theory.Models M nativeZF)
    {w D L zero mul A W plus T H x y a b : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ p, ¬ (Project.FirstOrderSemantics.reduct M).mem p zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hW : Carrier w D L W) (hAdd : AdditionGraph hM w plus)
    (hTable : ActionTable w D L zero mul A T) (hLaws : Laws w D L zero T H)
    (hx : Length w D L x a) (hy : Length w D L y b) (hDiv : Divides W H x y) :
    a = b ∨ (Project.FirstOrderSemantics.reduct M).mem a b := by
  obtain ⟨q,hq,hprod⟩ := hDiv
  obtain ⟨c,hc⟩ := exists_length ((hW q).mp hq)
  have hLen := product_length hM hw hz hzw hAdd hTable hLaws
    ((hW x).mpr (ConstructionMergerWordLength.length_raw hx)) hprod hx hc hy
  exact (ConstructionBaseMonoid.le_iff hM hw hAdd hx.1 hy.1).mp ⟨c,hc.1,hLen⟩

theorem snoc_not_dvd_prefix (hM : FirstOrder.Theory.Models M nativeZF)
    {w D L zero mul A W plus T H z pref q : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ p, ¬ (Project.FirstOrderSemantics.reduct M).mem p zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hW : Carrier w D L W) (hAdd : AdditionGraph hM w plus)
    (hTable : ActionTable w D L zero mul A T) (hLaws : Laws w D L zero T H)
    (hCons : Cons w D L z pref q) : ¬ Divides W H q pref := by
  intro hDiv
  have hZF := ModelTransfer.project_models_iff.mp hM
  obtain ⟨n,m,hn,hm,hSucc⟩ := cons_lengths hCons
  rcases length_le_of_dvd hM hw hz hzw hW hAdd hTable hLaws hm hn hDiv with he | hmn
  · exact KP.mem_irrefl_d (ZF.modelsKP hZF) n (he ▸ hSucc.predecessor_mem)
  · have hnOrd := hw.members_areOrdinals hZF n hn.1
    exact KP.mem_irrefl_d (ZF.modelsKP hZF) n (hnOrd.transitive m hmn n hSucc.predecessor_mem)

theorem snoc_not_dvd_old (hM : FirstOrder.Theory.Models M nativeZF)
    {w D L zero mul A W B H T z pref q m oldm : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ p, ¬ (Project.FirstOrderSemantics.reduct M).mem p zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hW : Carrier w D L W) (hB : Representatives W W B) (hH : MapsTo B W H)
    (hTable : ActionTable w D L zero mul A T) (hLaws : Laws w D L zero T H)
    (hCons : Cons w D L z pref q) (hOld : Old zero D m oldm) : ¬ Divides W H q oldm := by
  rintro ⟨r,_,hprod⟩
  obtain ⟨_,_,hOldQ,_,_⟩ := ConstructionMergerWordMonoid.factors_of_old hM hw hz hzw hW hB hH hTable hLaws hOld hprod
  exact ConstructionProbeRaw.old_ne_cons hz hOldQ hCons

def coneAt {m0 : Nat} (W H x y j b : Fin m0) : Project.Formula 1 m0 :=
  .iff (.conj (ProjectSyntax.encode id (ConstructionBaseMonoid.divides W H x b))
    (ProjectSyntax.encode id (ConstructionBaseMonoid.divides W H y b)))
    (ProjectSyntax.encode id (ConstructionBaseMonoid.divides W H j b))

theorem coneAt_freeClosed {m0 : Nat} (W H x y j b : Fin m0) : (coneAt W H x y j b).FreeClosed := by
  simp -implicitDefEqProofs [coneAt,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed]

theorem coneAt_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m0 : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m0) (W H x y j b : Fin m0) :
    Project.Formula.satisfies env (coneAt W H x y j b) ↔
      (Divides (env.bound W) (env.bound H) (env.bound x) (env.bound b) ∧
        Divides (env.bound W) (env.bound H) (env.bound y) (env.bound b) ↔
          Divides (env.bound W) (env.bound H) (env.bound j) (env.bound b)) := by
  simp only [coneAt,Project.Formula.satisfies_iff_iff,Project.Formula.satisfies_conj_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ConstructionBaseMonoid.divides_semantics (M := M)]
  rfl

theorem snoc_cone_intersection (hM : FirstOrder.Theory.Models M nativeZF)
    {w D L zero mul A W B H T plus z t j pref sz st sj : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ p, ¬ (Project.FirstOrderSemantics.reduct M).mem p zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hW : Carrier w D L W) (hB : Representatives W W B) (hH : MapsTo B W H)
    (hAdd : AdditionGraph hM w plus) (hTable : ActionTable w D L zero mul A T) (hLaws : Laws w D L zero T H)
    (hZ : Cons w D L z pref sz) (hT : Cons w D L t pref st) (hJ : Cons w D L j pref sj)
    (hCone : ∀ d, (Project.FirstOrderSemantics.reduct M).mem d L →
      (Reaches D A z d ∧ Reaches D A t d ↔ Reaches D A j d)) : JoinProperty W H sz st sj := by
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 5 := {
    bound := fun i => match i with | 0 => W | 1 => H | 2 => sz | 3 => st | _ => sj,
    free := fun _ => w }
  let p : Project.UnarySchema 5 := { body := coneAt 1 2 3 4 5 0,freeClosed := coneAt_freeClosed _ _ _ _ _ _ }
  have he (b) : p.denote env b ↔ (Divides W H sz b ∧ Divides W H st b ↔ Divides W H sj b) :=
    coneAt_semantics hM (env.push b) 1 2 3 4 5 0
  have hAll := ConstructionProbeEvaluationLaws.raw_induction hM env p hw hz hzw (by
    intro m b hOld
    apply (he b).mpr
    have hzOld := snoc_not_dvd_old hM hw hz hzw hW hB hH hTable hLaws hZ hOld
    have htOld := snoc_not_dvd_old hM hw hz hzw hW hB hH hTable hLaws hT hOld
    have hjOld := snoc_not_dvd_old hM hw hz hzw hW hB hH hTable hLaws hJ hOld
    simp only [hzOld,htOld,hjOld,false_and]) (by
    intro d a b hCons ih
    apply (he b).mpr
    rw [snoc_dvd_snoc_iff hM hw hz hzw hW hTable hLaws hZ hCons,
      snoc_dvd_snoc_iff hM hw hz hzw hW hTable hLaws hT hCons,
      snoc_dvd_snoc_iff hM hw hz hzw hW hTable hLaws hJ hCons]
    by_cases hEq : pref = a
    · subst a
      have hd : (Project.FirstOrderSemantics.reduct M).mem d L := by
        obtain ⟨_,_,_,_,_,_,_,_,_,_,_,hd,_,_,_⟩ := hCons
        exact hd
      have hzPref := snoc_not_dvd_prefix hM hw hz hzw hW hAdd hTable hLaws hZ
      have htPref := snoc_not_dvd_prefix hM hw hz hzw hW hAdd hTable hLaws hT
      have hjPref := snoc_not_dvd_prefix hM hw hz hzw hW hAdd hTable hLaws hJ
      simpa only [hzPref,htPref,hjPref,false_or,true_and] using hCone d hd
    · simpa only [hEq,false_and,or_false] using (he a).mp ih)
  intro b hb
  exact (he b).mp (hAll b ((hW b).mp hb))

def joinAt {m0 : Nat} (W H a : Fin m0) : Project.Formula 1 m0 :=
  (.forallE (.forallE (.imp (.mem (.bound 1) (.bound W.succ.succ)) (.imp (.mem (.bound 0) (.bound W.succ.succ)) (.imp (ProjectSyntax.encode id (ConstructionBaseMonoid.divides W.succ.succ H.succ.succ 1 a.succ.succ)) (.imp (ProjectSyntax.encode id (ConstructionBaseMonoid.divides W.succ.succ H.succ.succ 0 a.succ.succ)) (.existsE (.conj (.mem (.bound 0) (.bound W.succ.succ.succ)) (joinProperty W.succ.succ.succ H.succ.succ.succ 2 1 0)))))))))

theorem joinAt_freeClosed {m0 : Nat} (W H a : Fin m0) : (joinAt W H a).FreeClosed := by
  simp -implicitDefEqProofs [joinAt,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,joinProperty_freeClosed]

theorem joinAt_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m0 : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m0) (W H a : Fin m0) :
    Project.Formula.satisfies env (joinAt W H a) ↔ ∀ x y,
      (Project.FirstOrderSemantics.reduct M).mem x (env.bound W) →
      (Project.FirstOrderSemantics.reduct M).mem y (env.bound W) →
      Divides (env.bound W) (env.bound H) x (env.bound a) → Divides (env.bound W) (env.bound H) y (env.bound a) →
        ∃ j, (Project.FirstOrderSemantics.reduct M).mem j (env.bound W) ∧ JoinProperty (env.bound W) (env.bound H) x y j := by
  simp only [joinAt,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_mem_iff,
    Project.Term.eval_bound,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ConstructionBaseMonoid.divides_semantics (M := M),joinProperty_semantics hM]
  rfl

theorem exists_cone_join (hM : FirstOrder.Theory.Models M nativeZF)
    {w D L zero mul A W B H T plus unit : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ p, ¬ (Project.FirstOrderSemantics.reduct M).mem p zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hW : Carrier w D L W) (hB : Representatives W W B) (hH : MapsTo B W H)
    (hAdd : AdditionGraph hM w plus) (hTable : ActionTable w D L zero mul A T) (hLaws : Laws w D L zero T H)
    (hmW : LeftCancelMonoid W H unit) (hOldJoins : ConditionalJoins D mul) (hLetters : HasConeJoins D L A) :
    ConditionalJoins W H := by
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 2 := {
    bound := Fin.cases W (fun _ => H),free := fun _ => w }
  let p : Project.UnarySchema 2 := { body := joinAt 1 2 0,freeClosed := joinAt_freeClosed _ _ _ }
  have he (a) : p.denote env a ↔ ∀ x y, (Project.FirstOrderSemantics.reduct M).mem x W →
      (Project.FirstOrderSemantics.reduct M).mem y W → Divides W H x a → Divides W H y a →
        ∃ j, (Project.FirstOrderSemantics.reduct M).mem j W ∧ JoinProperty W H x y j := joinAt_semantics hM (env.push a) 1 2 0
  have hAll := ConstructionProbeEvaluationLaws.raw_induction hM env p hw hz hzw (by
    intro m a hOld
    apply (he a).mpr
    intro x y _ _ hxa hya
    obtain ⟨qx,_,hqx⟩ := hxa
    obtain ⟨qy,_,hqy⟩ := hya
    obtain ⟨r,s,hR,hS,hrm⟩ := ConstructionMergerWordMonoid.factors_of_old hM hw hz hzw hW hB hH hTable hLaws hOld hqx
    obtain ⟨t,u,hT,hU,htm⟩ := ConstructionMergerWordMonoid.factors_of_old hM hw hz hzw hW hB hH hTable hLaws hOld hqy
    obtain ⟨j,hj,hJoin⟩ := hOldJoins r t m hR.1 hT.1 hOld.1 ⟨s,hS.1,hrm⟩ ⟨u,hU.1,htm⟩
    obtain ⟨oj,hJ⟩ := ConstructionProbeRaw.exists_old hM (zero := zero) hj
    exact ⟨oj,(hW oj).mpr (ConstructionProbeRaw.old_raw hM hz hzw hJ),
      preserve_old_cone_intersection hM hw hz hzw hW hB hH hTable hLaws hR hT hJ hJoin⟩) (by
    intro d pref a hCons ih
    apply (he a).mpr
    intro x y hx hy hxa hya
    rcases (dvd_snoc_iff hM hw hz hzw hW hTable hLaws hCons).mp hxa with hxPref | ⟨z,hZ,hzd⟩
    · rcases (dvd_snoc_iff hM hw hz hzw hW hTable hLaws hCons).mp hya with hyPref | ⟨t,hT,htd⟩
      · exact (he pref).mp ih x y hx hy hxPref hyPref
      · have hxy := (dvd_snoc_iff hM hw hz hzw hW hTable hLaws hT).mpr (Or.inl hxPref)
        exact ⟨y,hy,fun b _ => ⟨And.right,fun h => ⟨divides_trans hmW hx hxy h,h⟩⟩⟩
    · rcases (dvd_snoc_iff hM hw hz hzw hW hTable hLaws hCons).mp hya with hyPref | ⟨t,hT,htd⟩
      · have hyx := (dvd_snoc_iff hM hw hz hzw hW hTable hLaws hZ).mpr (Or.inl hyPref)
        exact ⟨x,hx,fun b _ => ⟨And.left,fun h => ⟨h,divides_trans hmW hy hyx h⟩⟩⟩
      · have hzL : (Project.FirstOrderSemantics.reduct M).mem z L := by
          obtain ⟨_,_,_,_,_,_,_,_,_,_,_,hzL,_,_,_⟩ := hZ
          exact hzL
        have htL : (Project.FirstOrderSemantics.reduct M).mem t L := by
          obtain ⟨_,_,_,_,_,_,_,_,_,_,_,htL,_,_,_⟩ := hT
          exact htL
        have hdL : (Project.FirstOrderSemantics.reduct M).mem d L := by
          obtain ⟨_,_,_,_,_,_,_,_,_,_,_,hdL,_,_,_⟩ := hCons
          exact hdL
        obtain ⟨j,hj,hCone⟩ := hLetters z t d hzL htL hdL hzd htd
        obtain ⟨sj,hJ⟩ := ConstructionProbeRaw.exists_cons hM hw hj (ConstructionProbeRaw.cons_raw hCons).1
        exact ⟨sj,(hW sj).mpr (ConstructionProbeRaw.cons_raw hJ).2,
          snoc_cone_intersection hM hw hz hzw hW hB hH hAdd hTable hLaws hZ hT hJ hCone⟩)
  intro x y a hx hy ha hxa hya
  exact (he a).mp (hAll a ((hW a).mp ha)) x y hx hy hxa hya

theorem exists_system (hM : FirstOrder.Theory.Models M nativeZF)
    {w n D mul e P zero : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ p, ¬ (Project.FirstOrderSemantics.reduct M).mem p zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hm : LeftCancelMonoid D mul e) (hc : ForcingDiagramPoset.Conical D mul e)
    (hJoins : ConditionalJoins D mul)
    (hP : ConstructionMergerRelations.Prescription n D P) (hValid : ConstructionMergerRelations.Valid n D mul P) :
    ∃ C L projection K A W I T B H unit, (Representatives n D C ∧ MapsTo C L projection ∧
      ConstructionMergerCopies.Copies n D mul P C L ∧ ConstructionMergerCopies.Projection n D mul P C projection ∧
      ConstructionMergerCopies.EqualityLaw n D mul P projection ∧ Representatives L D K ∧ MapsTo K L A ∧
      ConstructionMergerAction.ActionTable D mul projection A ∧ ConstructionMergerAction.RightFreeAction mul e L A ∧
      ConstructionMergerAction.CopyLaw D mul projection A ∧ Carrier w D L W ∧
      Representatives W D I ∧ MapsTo I W T ∧ ConstructionMergerWordAction.ActionTable w D L zero mul A T ∧
      ConstructionMergerAction.RightFreeAction mul e W T ∧ Representatives W W B ∧ MapsTo B W H ∧ Laws w D L zero T H) ∧
      ConstructionProbeRaw.Old zero D e unit ∧ LeftCancelMonoid W H unit ∧ ForcingDiagramPoset.Conical W H unit ∧ HasConeJoins D L A ∧ ConditionalJoins W H := by
  obtain ⟨C,L,projection,K,A,W,I,T,B,H,unit,hParent,hUnit,hMonoid,hCon,hCone⟩ :=
    ConstructionMergerCopyCones.exists_system hM hw hz hzw hm hc hJoins hP hValid
  have hRetained := hParent
  obtain ⟨hC,hp,hL,hProjection,hEq,hK,hA,hTable,hFree,hCopy,hW,hI,hT,hWordTable,hWordFree,hB,hH,hLaws⟩ := hParent
  obtain ⟨plus,hAdd⟩ := ConstructionBaseMonoid.exists_additionGraph hM hw
  exact ⟨C,L,projection,K,A,W,I,T,B,H,unit,hRetained,hUnit,hMonoid,hCon,hCone,
    exists_cone_join hM hw hz hzw hW hB hH hAdd hWordTable hLaws hMonoid hJoins hCone⟩

end PPAC.Migration.ConstructionMergerWordCones
