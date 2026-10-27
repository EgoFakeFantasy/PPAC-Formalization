/- Pinned MergerWords.exists_cone_residual:45 and prescribed Copies cone
intersections / copies_hasConeJoins. Reuse the EXISTING generic left_mul_dvd_iff
and old ConditionalJoins. The overlap relation itself is used, no closure.
Consumer: original Merger Word conditional-join construction. -/
import PPAC.Migration.ConstructionMergerWordCancellation

namespace PPAC.Migration.ConstructionMergerCopyCones
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionMergerRelations (Prescription Start product_range)
open ConstructionMergerCopies (Copies Projection EqualityLaw copy_eq_iff copy_injective representative)
open ConstructionMergerAction (CopyLaw RightFreeAction)
open ConstructionProbeLetters (Representatives)
open ConstructionProbeAction (projected projected_indices projected_range)
open ConstructionProbeCones (JoinProperty)
open ConstructionProbeSharedIntersections (ConditionalJoins)
open ConstructionProbeConditionalJoins (left_mul_dvd_iff)
open ConstructionBaseMonoid (Divides)
open ConstructionProbeRaw (Carrier)
open ConstructionMergerWordProduct (Laws)
open ForcingDiagramOrder (Product product product_semantics)
open ForcingDiagramPoset (LeftCancelMonoid)
open ForcingSupportSize (MapsTo)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def Reaches (D A z v : M.Carrier .set) : Prop :=
  ∃ m, (Project.FirstOrderSemantics.reduct M).mem m D ∧ Product A z m v

def HasConeJoins (D L A : M.Carrier .set) : Prop := ∀ z v c,
  (Project.FirstOrderSemantics.reduct M).mem z L → (Project.FirstOrderSemantics.reduct M).mem v L →
  (Project.FirstOrderSemantics.reduct M).mem c L → Reaches D A z c → Reaches D A v c →
    ∃ j, (Project.FirstOrderSemantics.reduct M).mem j L ∧ ∀ b,
      (Project.FirstOrderSemantics.reduct M).mem b L → (Reaches D A z b ∧ Reaches D A v b ↔ Reaches D A j b)

theorem exists_cone_residual {D mul e x a c ac : M.Carrier .set}
    (hm : LeftCancelMonoid D mul e) (hJ : ConditionalJoins D mul)
    (hx : (Project.FirstOrderSemantics.reduct M).mem x D) (ha : (Project.FirstOrderSemantics.reduct M).mem a D)
    (hc : (Project.FirstOrderSemantics.reduct M).mem c D) (hac : Product mul a c ac) (hxc : Divides D mul x ac) :
    ∃ r, (Project.FirstOrderSemantics.reduct M).mem r D ∧ ∀ t atv,
      (Project.FirstOrderSemantics.reduct M).mem t D → Product mul a t atv →
        (Divides D mul x atv ↔ Divides D mul r t) := by
  obtain ⟨s,hs,hJoin⟩ := hJ x a ac hx ha (product_range hm ha hc hac) hxc ⟨c,hc,hac⟩
  have hSelf : Divides D mul s s := ⟨e,hm.1.1,((hm.1.2 s hs s).2).mpr rfl⟩
  obtain ⟨r,hr,har⟩ := ((hJoin s hs).mpr hSelf).2
  refine ⟨r,hr,?_⟩
  intro t atv ht hat
  have hCanc := left_mul_dvd_iff hm ha hr ht har hat
  constructor
  · intro hxt
    exact hCanc.mp ((hJoin atv (product_range hm ha ht hat)).mp ⟨hxt,⟨t,ht,hat⟩⟩)
  · intro hrt
    exact ((hJoin atv (product_range hm ha ht hat)).mpr (hCanc.mpr hrt)).1

theorem reaches_refl {D L mul e A z : M.Carrier .set}
    (hm : LeftCancelMonoid D mul e) (hFree : RightFreeAction mul e L A)
    (hz : (Project.FirstOrderSemantics.reduct M).mem z L) : Reaches D A z z :=
  ⟨e,hm.1.1,hFree.1 z hz⟩

theorem reaches_trans {D L mul e A z v c : M.Carrier .set}
    (hm : LeftCancelMonoid D mul e) (hFree : RightFreeAction mul e L A)
    (h1 : Reaches D A z v) (h2 : Reaches D A v c) : Reaches D A z c := by
  obtain ⟨m,hmD,hzm⟩ := h1
  obtain ⟨n,hnD,hvn⟩ := h2
  obtain ⟨mn,hmnD,hmn⟩ := (hm.2.1 m hmD).1 n hnD
  exact ⟨mn,hmnD,hFree.2.1 z m n mn v c hmn hzm hvn⟩

theorem reaches_copy_iff {n D mul e C L projection A i x cx z : M.Carrier .set}
    (hm : LeftCancelMonoid D mul e) (hC : Representatives n D C) (hp : MapsTo C L projection)
    (hCopy : CopyLaw D mul projection A) (hcx : Product projection i x cx) :
    Reaches D A cx z ↔ ∃ m xm, (Project.FirstOrderSemantics.reduct M).mem m D ∧
      Product mul x m xm ∧ Product projection i xm z := by
  constructor
  · rintro ⟨m,hmD,hAct⟩
    obtain ⟨xm,_,hxm⟩ := (hm.2.1 x (projected_indices hC hp hcx).2).1 m hmD
    exact ⟨m,xm,hmD,hxm,(hCopy i x xm cx m z hmD hcx hxm).mp hAct⟩
  · rintro ⟨m,xm,hmD,hxm,hxmp⟩
    exact ⟨m,hmD,(hCopy i x xm cx m z hmD hcx hxm).mpr hxmp⟩

theorem reaches_same_copy_iff {n D mul e P C L projection A i x y cx cy : M.Carrier .set}
    (hm : LeftCancelMonoid D mul e) (hC : Representatives n D C) (hp : MapsTo C L projection)
    (hEq : EqualityLaw n D mul P projection) (hCopy : CopyLaw D mul projection A)
    (hcx : Product projection i x cx) (hcy : Product projection i y cy) :
    Reaches D A cx cy ↔ Divides D mul x y := by
  constructor
  · intro h
    obtain ⟨m,xm,hmD,hxm,hxmP⟩ := (reaches_copy_iff hm hC hp hCopy hcx).mp h
    have he := copy_injective hC hp hEq hxmP hcy
    exact ⟨m,hmD,he ▸ hxm⟩
  · rintro ⟨m,hmD,hxm⟩
    exact ⟨m,hmD,(hCopy i x y cx m cy hmD hcx hxm).mpr hcy⟩

theorem same_copy_cone_intersection {n D mul e P C L projection A i x y j cx cy cj : M.Carrier .set}
    (hm : LeftCancelMonoid D mul e) (hC : Representatives n D C) (hp : MapsTo C L projection)
    (hEq : EqualityLaw n D mul P projection) (hCopy : CopyLaw D mul projection A)
    (hFree : RightFreeAction mul e L A) (hcx : Product projection i x cx)
    (hcy : Product projection i y cy) (hcj : Product projection i j cj) (hJoin : JoinProperty D mul x y j) :
    ∀ b, Reaches D A cx b ∧ Reaches D A cy b ↔ Reaches D A cj b := by
  intro b
  constructor
  · rintro ⟨hx,hy⟩
    obtain ⟨m,xm,hmD,hxm,hxmP⟩ := (reaches_copy_iff hm hC hp hCopy hcx).mp hx
    obtain ⟨k,yk,hkD,hyk,hykP⟩ := (reaches_copy_iff hm hC hp hCopy hcy).mp hy
    have he := copy_injective hC hp hEq hxmP hykP
    have hxmD := product_range hm (projected_indices hC hp hcx).2 hmD hxm
    have hDiv := (hJoin xm hxmD).mp ⟨⟨m,hmD,hxm⟩,⟨k,hkD,he.symm ▸ hyk⟩⟩
    exact (reaches_same_copy_iff hm hC hp hEq hCopy hcj hxmP).mpr hDiv
  · intro h
    have hjD := (projected_indices hC hp hcj).2
    have hSelf : Divides D mul j j := ⟨e,hm.1.1,((hm.1.2 j hjD j).2).mpr rfl⟩
    have hxy := (hJoin j hjD).mpr hSelf
    exact ⟨reaches_trans hm hFree ((reaches_same_copy_iff hm hC hp hEq hCopy hcx hcj).mpr hxy.1) h,
      reaches_trans hm hFree ((reaches_same_copy_iff hm hC hp hEq hCopy hcy hcj).mpr hxy.2) h⟩

theorem overlap_cone_intersection (hM : FirstOrder.Theory.Models M nativeZF)
    {n D mul e P C L projection A i j a b x y cx cy z : M.Carrier .set}
    (hm : LeftCancelMonoid D mul e) (hP : Prescription n D P)
    (hC : Representatives n D C) (hp : MapsTo C L projection)
    (hEq : EqualityLaw n D mul P projection) (hCopy : CopyLaw D mul projection A)
    (hij : i ≠ j) (hab : Start P i j a b)
    (hcx : Product projection i x cx) (hcy : Product projection j y cy) :
    Reaches D A cx z ∧ Reaches D A cy z ↔
      ∃ t atv bt, (Project.FirstOrderSemantics.reduct M).mem t D ∧ Product mul a t atv ∧ Product mul b t bt ∧
        Divides D mul x atv ∧ Divides D mul y bt ∧ Product projection i atv z := by
  constructor
  · rintro ⟨hx,hy⟩
    obtain ⟨m,xm,hmD,hxm,hxmP⟩ := (reaches_copy_iff hm hC hp hCopy hcx).mp hx
    obtain ⟨k,yk,hkD,hyk,hykP⟩ := (reaches_copy_iff hm hC hp hCopy hcy).mp hy
    have hRel := (copy_eq_iff hEq hxmP hykP).mp rfl
    rcases hRel.2.2.2.2 with ⟨he,_⟩ | ⟨_,a',b',t,hStart,ht,hat,hbt⟩
    · exact (hij he).elim
    · obtain ⟨rfl,rfl⟩ := hP.2 i j a b a' b' hab hStart
      exact ⟨t,xm,yk,ht,hat,hbt,⟨m,hmD,hxm⟩,⟨k,hkD,hyk⟩,hxmP⟩
  · rintro ⟨t,atv,bt,ht,hat,hbt,hx,hy,hatz⟩
    have hSpec := hP.1 i j a b hab
    have hAtD := product_range hm hSpec.2.2.1 ht hat
    have hBtD := product_range hm hSpec.2.2.2 ht hbt
    obtain ⟨q,_,hbtq⟩ := projected hM hC hp hSpec.2.1 hBtD
    have hRel : ConstructionMergerRelations.CopyRel n D mul P i atv j bt :=
      ⟨hSpec.1,hAtD,hSpec.2.1,hBtD,Or.inr ⟨hij,a,b,t,hab,ht,hat,hbt⟩⟩
    have heq := (copy_eq_iff hEq hatz hbtq).mpr hRel
    exact ⟨(reaches_same_copy_iff hm hC hp hEq hCopy hcx hatz).mpr hx,
      (reaches_same_copy_iff hm hC hp hEq hCopy hcy (heq.symm ▸ hbtq)).mpr hy⟩

theorem copies_hasConeJoins (hM : FirstOrder.Theory.Models M nativeZF)
    {n D mul e P C L projection A : M.Carrier .set}
    (hm : LeftCancelMonoid D mul e) (hP : Prescription n D P)
    (hC : Representatives n D C) (hL : Copies n D mul P C L) (hp : MapsTo C L projection)
    (hProjection : Projection n D mul P C projection) (hEq : EqualityLaw n D mul P projection)
    (hCopy : CopyLaw D mul projection A) (hFree : RightFreeAction mul e L A)
    (hJ : ConditionalJoins D mul) : HasConeJoins D L A := by
  intro z v c hz hv _ hzc hvc
  obtain ⟨i,x,hi,hx,hcx⟩ := representative hC hL hProjection hz
  obtain ⟨j,y,hj,hy,hcy⟩ := representative hC hL hProjection hv
  by_cases hij : i = j
  · subst j
    obtain ⟨u,xu,hu,hxu,hxuP⟩ := (reaches_copy_iff hm hC hp hCopy hcx).mp hzc
    obtain ⟨t,yt,ht,hyt,hytP⟩ := (reaches_copy_iff hm hC hp hCopy hcy).mp hvc
    have he := copy_injective hC hp hEq hxuP hytP
    obtain ⟨k,hk,hJoin⟩ := hJ x y xu hx hy (product_range hm hx hu hxu) ⟨u,hu,hxu⟩ ⟨t,ht,he.symm ▸ hyt⟩
    obtain ⟨ck,hck,hkc⟩ := projected hM hC hp hi hk
    exact ⟨ck,hck,fun b _ => same_copy_cone_intersection hm hC hp hEq hCopy hFree hcx hcy hkc hJoin b⟩
  · obtain ⟨u,xu,hu,hxu,hxuP⟩ := (reaches_copy_iff hm hC hp hCopy hcx).mp hzc
    obtain ⟨t,yt,ht,hyt,hytP⟩ := (reaches_copy_iff hm hC hp hCopy hcy).mp hvc
    have hRel := (copy_eq_iff hEq hxuP hytP).mp rfl
    rcases hRel.2.2.2.2 with ⟨he,_⟩ | ⟨_,a,b,t0,hab,ht0,hat0,hbt0⟩
    · exact (hij he).elim
    · have hSpec := hP.1 i j a b hab
      obtain ⟨r,hrD,hr⟩ := exists_cone_residual hm hJ hx hSpec.2.2.1 ht0 hat0 ⟨u,hu,hxu⟩
      obtain ⟨s,hsD,hs⟩ := exists_cone_residual hm hJ hy hSpec.2.2.2 ht0 hbt0 ⟨t,ht,hyt⟩
      obtain ⟨k,hk,hJoin⟩ := hJ r s t0 hrD hsD ht0
        ((hr t0 xu ht0 hat0).mp ⟨u,hu,hxu⟩) ((hs t0 yt ht0 hbt0).mp ⟨t,ht,hyt⟩)
      obtain ⟨ak,hakD,hak⟩ := (hm.2.1 a hSpec.2.2.1).1 k hk
      obtain ⟨ck,hck,hakP⟩ := projected hM hC hp hi hakD
      refine ⟨ck,hck,?_⟩
      intro q _
      have hCross := overlap_cone_intersection hM hm hP hC hp hEq hCopy hij hab (z := q) hcx hcy
      constructor
      · intro hq
        obtain ⟨t,atv,bt,ht,hat,hbt,hxat,hybt,hatP⟩ := hCross.mp hq
        have hkt := (hJoin t ht).mp ⟨(hr t atv ht hat).mp hxat,(hs t bt ht hbt).mp hybt⟩
        have hDiv := (left_mul_dvd_iff hm hSpec.2.2.1 hk ht hak hat).mpr hkt
        exact (reaches_same_copy_iff hm hC hp hEq hCopy hakP hatP).mpr hDiv
      · intro hq
        obtain ⟨m,akm,hmD,hakm,hakmP⟩ := (reaches_copy_iff hm hC hp hCopy hakP).mp hq
        obtain ⟨km,hkmD,hkm⟩ := (hm.2.1 k hk).1 m hmD
        have hAkm := (hm.2.2 a k m ak km akm hSpec.2.2.1 hk hmD hak hkm).mp hakm
        obtain ⟨bkm,hbkmD,hBkm⟩ := (hm.2.1 b hSpec.2.2.2).1 km hkmD
        have hRS := (hJoin km hkmD).mpr ⟨m,hmD,hkm⟩
        exact hCross.mpr ⟨km,akm,bkm,hkmD,hAkm,hBkm,(hr km akm hkmD hAkm).mpr hRS.1,
          (hs km bkm hkmD hBkm).mpr hRS.2,hakmP⟩

def reaches {m0 : Nat} (D A z v : Fin m0) : Project.Formula 1 m0 :=
  (.existsE (.conj (.mem (.bound 0) (.bound D.succ)) (ProjectSyntax.encode id (ForcingDiagramOrder.product
  A.succ z.succ 0 v.succ))))

theorem reaches_freeClosed {m0 : Nat} (D A z v : Fin m0) : (reaches D A z v).FreeClosed := by
  simp -implicitDefEqProofs [reaches,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed]

theorem reaches_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m0 : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m0) (D A z v : Fin m0) :
    Project.Formula.satisfies env (reaches D A z v) ↔ Reaches (env.bound D) (env.bound A) (env.bound z) (env.bound v) := by
  simp only [reaches,Reaches,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),product_semantics (M := M)]
  rfl

def hasConeJoins {m0 : Nat} (D L A : Fin m0) : Project.Formula 1 m0 :=
  (.forallE (.forallE (.forallE (.imp (.mem (.bound 2) (.bound L.succ.succ.succ)) (.imp (.mem (.bound 1)
  (.bound L.succ.succ.succ)) (.imp (.mem (.bound 0) (.bound L.succ.succ.succ)) (.imp (reaches
  D.succ.succ.succ A.succ.succ.succ 2 0) (.imp (reaches D.succ.succ.succ A.succ.succ.succ 1 0) (.existsE
  (.conj (.mem (.bound 0) (.bound L.succ.succ.succ.succ)) (.forallE (.imp (.mem (.bound 0) (.bound
  L.succ.succ.succ.succ.succ)) (.iff (.conj (reaches D.succ.succ.succ.succ.succ A.succ.succ.succ.succ.succ 4
  0) (reaches D.succ.succ.succ.succ.succ A.succ.succ.succ.succ.succ 3 0)) (reaches
  D.succ.succ.succ.succ.succ A.succ.succ.succ.succ.succ 1 0))))))))))))))

theorem hasConeJoins_freeClosed {m0 : Nat} (D L A : Fin m0) : (hasConeJoins D L A).FreeClosed := by
  simp -implicitDefEqProofs [hasConeJoins,Definitional.Formula.FreeClosed,reaches_freeClosed]

theorem hasConeJoins_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m0 : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m0) (D L A : Fin m0) :
    Project.Formula.satisfies env (hasConeJoins D L A) ↔ HasConeJoins (env.bound D) (env.bound L) (env.bound A) := by
  simp only [hasConeJoins,HasConeJoins,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_iff_iff,
    Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,reaches_semantics hM]
  rfl

theorem exists_system (hM : FirstOrder.Theory.Models M nativeZF)
    {w n D mul e P zero : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ p, ¬ (Project.FirstOrderSemantics.reduct M).mem p zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hm : LeftCancelMonoid D mul e) (hc : ForcingDiagramPoset.Conical D mul e)
    (hJoins : ConditionalJoins D mul)
    (hP : Prescription n D P) (hValid : ConstructionMergerRelations.Valid n D mul P) :
    ∃ C L projection K A W I T B H unit, (Representatives n D C ∧ MapsTo C L projection ∧
      ConstructionMergerCopies.Copies n D mul P C L ∧ ConstructionMergerCopies.Projection n D mul P C projection ∧
      ConstructionMergerCopies.EqualityLaw n D mul P projection ∧ Representatives L D K ∧ MapsTo K L A ∧
      ConstructionMergerAction.ActionTable D mul projection A ∧ ConstructionMergerAction.RightFreeAction mul e L A ∧
      ConstructionMergerAction.CopyLaw D mul projection A ∧ Carrier w D L W ∧
      Representatives W D I ∧ MapsTo I W T ∧ ConstructionMergerWordAction.ActionTable w D L zero mul A T ∧
      ConstructionMergerAction.RightFreeAction mul e W T ∧ Representatives W W B ∧ MapsTo B W H ∧ Laws w D L zero T H) ∧
      ConstructionProbeRaw.Old zero D e unit ∧ LeftCancelMonoid W H unit ∧ ForcingDiagramPoset.Conical W H unit ∧ HasConeJoins D L A := by
  obtain ⟨C,L,projection,K,A,W,I,T,B,H,unit,hParent,hUnit,hMonoid,hCon⟩ :=
    ConstructionMergerWordCancellation.exists_system hM hw hz hzw hm hc hP hValid
  have hRetained := hParent
  obtain ⟨hC,hp,hL,hProjection,hEq,hK,hA,hTable,hFree,hCopy,hW,hI,hT,hWordTable,hWordFree,hB,hH,hLaws⟩ := hParent
  exact ⟨C,L,projection,K,A,W,I,T,B,H,unit,hRetained,hUnit,hMonoid,hCon,
    copies_hasConeJoins hM hm hP hC hL hp hProjection hEq hCopy hFree hJoins⟩

end PPAC.Migration.ConstructionMergerCopyCones
