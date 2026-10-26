/- Pinned ProbeGates.Word.cone_join -> Path.extension_hasConditionalJoins.
Reuse the stronger shared-gate theorem at native identity graphs. The actual
source old/different-head/equal-head cases then construct every Word join.
Consumer: ConservativeCells.Probe.extension, MonoidBase.ProbeData.monoid. -/
import PPAC.Migration.ConstructionProbeSharedGates
import PPAC.Migration.ConstructionProbeGeneratorSyntax

namespace PPAC.Migration.ConstructionProbeConditionalJoins
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionProbeRaw ConstructionProbeRawAction ConstructionProbeGates
open ConstructionProbeGatesSyntax (headSome headSome_freeClosed headSome_semantics gate gate_freeClosed gate_semantics)
open ConstructionProbeWord (WordCarrier word_raw)
open ConstructionProbeOldEmbedding (OldGraph old_word old_dvd_iff_headDiv)
open ConstructionProbeWordMonoid (MultiplicationGraph)
open ConstructionProbeAlphabet (Alphabet)
open ConstructionProbeAlphabetMap (AlphabetSimulation)
open ConstructionProbeConservative (Conservative)
open ConstructionProbeSharedIntersections (ConditionalJoins shared_intersections)
open ConstructionProbeLiftHom (PreservesProducts)
open ConstructionProbeWordTransport (WordGraph)
open ConstructionBaseMonoid (Divides)
open ForcingDiagramOrder (Product)
open ForcingDiagramPoset (LeftCancelMonoid)
open ForcingSupportSize (MapsTo)
open ForcingConditionGraphs (function_input Permutation IdentityGraph)
open ConstructionProbeCones (JoinProperty joinProperty joinProperty_freeClosed joinProperty_semantics)
open ForcingDiagramPoset (Conical)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

theorem identity_conservative {D mul f : M.Carrier .set}
    (hp : Permutation D f) (hi : IdentityGraph D f) : Conservative D D mul mul f := by
  refine ⟨⟨hp.1,hp.2.1⟩,?_,?_,?_⟩
  · intro x y z fx fy _ _ hz _
    exact ⟨z,(hi z z).mpr ⟨hz,rfl⟩⟩
  · intro x y j fx fy fj hx hy hj hJoin
    obtain ⟨_,rfl⟩ := (hi x fx).mp hx
    obtain ⟨_,rfl⟩ := (hi y fy).mp hy
    obtain ⟨_,rfl⟩ := (hi j fj).mp hj
    exact hJoin
  · intro x y fx fy hx hy hCommon
    obtain ⟨_,rfl⟩ := (hi x fx).mp hx
    obtain ⟨_,rfl⟩ := (hi y fy).mp hy
    exact hCommon

theorem identity_word_graph (hM : FirstOrder.Theory.Models M nativeZF)
    {w D S mul A b W f g H : M.Carrier .set}
    (hW : WordCarrier w D S mul A b W) (hf : MapsTo D D f)
    (hfId : IdentityGraph D f) (hgId : IdentityGraph S g) (hId : IdentityGraph W H) :
    WordGraph w D S S f g W H := by
  have self (q) (hq : (Project.FirstOrderSemantics.reduct M).mem q W) :
      ConstructionProbeRawTransport.Value w D S S f g q q := by
    obtain ⟨h,x,⟨n,hn,hh⟩,hx,hq⟩ := word_raw hW hq
    refine ⟨n,h,x,h,x,hn,hh,hx,hq,hh,hq,(hfId x x).mpr ⟨hx,rfl⟩,?_⟩
    intro i y
    constructor
    · intro hy
      exact ⟨y,hy,(hgId y y).mpr ⟨hh.2 i y hy,rfl⟩⟩
    · rintro ⟨z,hz,hzy⟩
      exact ((hgId z y).mp hzy).2 ▸ hz
  intro q r
  constructor
  · intro hqr
    obtain ⟨hq,rfl⟩ := (hId q r).mp hqr
    exact ⟨hq,self q hq⟩
  · rintro ⟨hq,hv⟩
    have he := ConstructionProbeRawTransport.value_unique hM hf hv (self q hq)
    subst r
    exact (hId q q).mpr ⟨hq,rfl⟩

theorem gate_existence (hM : FirstOrder.Theory.Models M nativeZF)
    {w D S zero mul A b W E e I G unit O : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ v, ¬ (Project.FirstOrderSemantics.reduct M).mem v zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hm : LeftCancelMonoid D mul e) (hAlpha : Alphabet D mul e S I A E)
    (hW : WordCarrier w D S mul A b W) (hb : (Project.FirstOrderSemantics.reduct M).mem b D)
    (hG : MultiplicationGraph hM w D S zero mul A b W E G) (hUnit : Old zero D e unit)
    (hO : OldGraph zero D O) (hJ : ConditionalJoins D mul) (hA : Conservative D W mul G O) :
    ∀ q s z, (Project.FirstOrderSemantics.reduct M).mem q W → HeadSome w D S q s →
      (Project.FirstOrderSemantics.reduct M).mem z W → Divides W G q z → ¬ HeadSome w D S z s →
      ∃ j, (Project.FirstOrderSemantics.reduct M).mem j D ∧ Gate w D S zero mul A W G q s j := by
  obtain ⟨f,hf,hfId⟩ := ForcingConditionGraphs.exists_identity hM D
  obtain ⟨g,hg,hgId⟩ := ForcingConditionGraphs.exists_identity hM S
  obtain ⟨H,hH,hHId⟩ := ForcingConditionGraphs.exists_identity hM W
  have hCons := identity_conservative (mul := mul) hf hfId
  have hPres : PreservesProducts mul mul f := by
    intro x y z fx fy fz hprod hx hy hz'
    obtain ⟨_,rfl⟩ := (hfId x fx).mp hx
    obtain ⟨_,rfl⟩ := (hfId y fy).mp hy
    obtain ⟨_,rfl⟩ := (hfId z fz).mp hz'
    exact hprod
  have hAlphaId : AlphabetSimulation S S A A E E f g := by
    refine ⟨⟨hg.1,hg.2.1⟩,?_,?_,?_⟩
    · intro x s t fx gs gt hprod hx hs ht
      obtain ⟨_,rfl⟩ := (hfId x fx).mp hx
      obtain ⟨_,rfl⟩ := (hgId s gs).mp hs
      obtain ⟨_,rfl⟩ := (hgId t gt).mp ht
      exact hprod
    · intro s z gs fz hsz hs hz'
      obtain ⟨_,rfl⟩ := (hgId s gs).mp hs
      obtain ⟨_,rfl⟩ := (hfId z fz).mp hz'
      exact hsz
    · intro x s fx gs hx hs
      obtain ⟨_,rfl⟩ := (hfId x fx).mp hx
      obtain ⟨_,rfl⟩ := (hgId s gs).mp hs
      exact Iff.rfl
  have hGraph := identity_word_graph hM hW hf.1 hfId hgId hHId
  intro q s z hq hHead hzW hqz hExit
  obtain ⟨tail,hTail⟩ := hHead
  have hs := cons_letter hTail
  obtain ⟨j,_,hj,_,hgate,_⟩ := ConstructionProbeSharedGates.exists_simulated_gate_of_exit hM hw hz hzw
    hm hm hAlpha hAlpha hCons hPres hAlphaId ((hfId b b).mpr ⟨hb,rfl⟩)
    hW hW hG hG hUnit hUnit hH.1 hGraph hO hO hJ hA hA
    q (word_raw hW hq) q s s z ((hHId q q).mpr ⟨hq,rfl⟩) ((hgId s s).mpr ⟨hs,rfl⟩)
    ⟨tail,hTail⟩ hzW hqz hExit
  exact ⟨j,hj,hgate⟩

def ExitGates (w D S zero mul A W G : M.Carrier .set) : Prop :=
  ∀ q s z, (Project.FirstOrderSemantics.reduct M).mem q W → HeadSome w D S q s →
    (Project.FirstOrderSemantics.reduct M).mem z W → Divides W G q z → ¬ HeadSome w D S z s →
    ∃ j, (Project.FirstOrderSemantics.reduct M).mem j D ∧ Gate w D S zero mul A W G q s j

/-- Source old intersections, expressed through the proved old_dvd_iff_headDiv. -/
def OldIntersections (w D S zero mul A W : M.Carrier .set) : Prop := ∀ x y z,
  (Project.FirstOrderSemantics.reduct M).mem x D → (Project.FirstOrderSemantics.reduct M).mem y D →
  (Project.FirstOrderSemantics.reduct M).mem z W → HeadDiv w D S zero mul A x z → HeadDiv w D S zero mul A y z →
  ∃ j, (Project.FirstOrderSemantics.reduct M).mem j D ∧ ∀ q, (Project.FirstOrderSemantics.reduct M).mem q W →
    ((HeadDiv w D S zero mul A x q ∧ HeadDiv w D S zero mul A y q) ↔ HeadDiv w D S zero mul A j q)

theorem old_intersections (hM : FirstOrder.Theory.Models M nativeZF)
    {w D S zero mul A b W E e I G O : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ v, ¬ (Project.FirstOrderSemantics.reduct M).mem v zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hm : LeftCancelMonoid D mul e) (hAlpha : Alphabet D mul e S I A E)
    (hW : WordCarrier w D S mul A b W) (hb : (Project.FirstOrderSemantics.reduct M).mem b D)
    (hG : MultiplicationGraph hM w D S zero mul A b W E G)
    (hO : OldGraph zero D O) (hJ : ConditionalJoins D mul) (hA : Conservative D W mul G O) :
    OldIntersections w D S zero mul A W := by
  intro x y z hx hy hzW hxz hyz
  obtain ⟨ox,hox,_⟩ := hA.1.1.1.2 x hx
  obtain ⟨oy,hoy,_⟩ := hA.1.1.1.2 y hy
  have divOld {a oa q} (ha : PureKuratowski.PairMember M a oa O) (hq : (Project.FirstOrderSemantics.reduct M).mem q W) :=
    old_dvd_iff_headDiv hM hw hz hzw hm hAlpha hW hb hG ((hO a oa).mp ha) hq
  obtain ⟨m,hmD,hxm,hym⟩ := hA.2.2.2 x y ox oy hox hoy ⟨z,hzW,(divOld hox hzW).mpr hxz,(divOld hoy hzW).mpr hyz⟩
  obtain ⟨j,hj,hjoin⟩ := hJ x y m hx hy hmD hxm hym
  obtain ⟨oj,hoj,_⟩ := hA.1.1.1.2 j hj
  have hjoinW := hA.2.2.1 x y j ox oy oj hox hoy hoj hjoin
  exact ⟨j,hj,fun q hq => ((and_congr (divOld hox hq).symm (divOld hoy hq).symm).trans (hjoinW q hq)).trans (divOld hoj hq)⟩

theorem dvd_of_different_head (hM : FirstOrder.Theory.Models M nativeZF)
    {w D S zero mul A W G x y z s t : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ v, ¬ (Project.FirstOrderSemantics.reduct M).mem v zero)
    (hGate : ExitGates w D S zero mul A W G)
    (hx : (Project.FirstOrderSemantics.reduct M).mem x W) (hy : (Project.FirstOrderSemantics.reduct M).mem y W)
    (hxs : HeadSome w D S x s) (hyt : HeadSome w D S y t) (hst : s ≠ t)
    (hzW : (Project.FirstOrderSemantics.reduct M).mem z W) (hyz : Divides W G y z) (hzs : HeadSome w D S z s) :
    Divides W G y x := by
  have hzt : ¬ HeadSome w D S z t := fun h => hst (head_unique hM hw hzs h)
  obtain ⟨j,_,hj⟩ := hGate y t z hy hyt hzW hyz hzt
  exact ((hj x hx).mpr ((headDiv_of_same_head hM hw hz hxs hzs).mpr ((hj z hzW).mp ⟨hyz,hzt⟩))).1

theorem old_word_cone_join (hM : FirstOrder.Theory.Models M nativeZF)
    {w D S zero mul A b W E e I G unit x ox y z : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ v, ¬ (Project.FirstOrderSemantics.reduct M).mem v zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hm : LeftCancelMonoid D mul e) (hAlpha : Alphabet D mul e S I A E)
    (hW : WordCarrier w D S mul A b W) (hb : (Project.FirstOrderSemantics.reduct M).mem b D)
    (hG : MultiplicationGraph hM w D S zero mul A b W E G) (hUnit : Old zero D e unit)
    (hOld : OldIntersections w D S zero mul A W) (hGate : ExitGates w D S zero mul A W G)
    (hox : Old zero D x ox) (hy : (Project.FirstOrderSemantics.reduct M).mem y W)
    (hzW : (Project.FirstOrderSemantics.reduct M).mem z W) (hxz : Divides W G ox z) (hyz : Divides W G y z) :
    ∃ j, (Project.FirstOrderSemantics.reduct M).mem j W ∧ JoinProperty W G ox y j := by
  have hmW := ConstructionProbeWordMonoid.monoid_laws hM hw hz hzw hm hAlpha hW hb hUnit hG
  have hoxW := old_word hM hz hzw hW hox
  have divOld {a oa q} (ha : Old zero D a oa) (hq : (Project.FirstOrderSemantics.reduct M).mem q W) :=
    old_dvd_iff_headDiv hM hw hz hzw hm hAlpha hW hb hG ha hq
  by_cases hxy : Divides W G ox y
  · exact ⟨y,hy,fun _ _ => ⟨And.right,fun h => ⟨divides_trans hmW hoxW hxy h,h⟩⟩⟩
  rcases cases_raw hM hw hz hzw (word_raw hW hy) with ⟨a,ha⟩ | ⟨s,t,hCons⟩
  · obtain ⟨k,hk,hjoin⟩ := hOld x a z hox.1 ha.1 hzW ((divOld hox hzW).mp hxz) ((divOld ha hzW).mp hyz)
    obtain ⟨j,hj⟩ := exists_old hM (zero := zero) hk
    exact ⟨j,old_word hM hz hzw hW hj,fun q hq =>
      ((and_congr (divOld hox hq) (divOld ha hq)).trans (hjoin q hq)).trans (divOld hj hq).symm⟩
  · have hHead : HeadSome w D S y s := ⟨t,hCons⟩
    have hn : ¬ HeadDiv w D S zero mul A x y := fun h => hxy ((divOld hox hy).mpr h)
    have hExit : ¬ HeadSome w D S z s := fun h => hn ((headDiv_of_same_head hM hw hz hHead h).mpr ((divOld hox hzW).mp hxz))
    obtain ⟨g,hg,hgate⟩ := hGate y s z hy hHead hzW hyz hExit
    obtain ⟨k,hk,hjoin⟩ := hOld x g z hox.1 hg hzW ((divOld hox hzW).mp hxz) ((hgate z hzW).mp ⟨hyz,hExit⟩)
    obtain ⟨j,hj⟩ := exists_old hM (zero := zero) hk
    refine ⟨j,old_word hM hz hzw hW hj,fun q hq => ?_⟩
    exact ((and_congr (divOld hox hq) Iff.rfl).trans (gate_old_intersection hM hw hz hgate hHead hn hq)).trans
      ((hjoin q hq).trans (divOld hj hq).symm)

theorem different_head_cone_join (hM : FirstOrder.Theory.Models M nativeZF)
    {w D S zero mul A b W E e I G unit x y z s t : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ v, ¬ (Project.FirstOrderSemantics.reduct M).mem v zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hm : LeftCancelMonoid D mul e) (hAlpha : Alphabet D mul e S I A E)
    (hW : WordCarrier w D S mul A b W) (hb : (Project.FirstOrderSemantics.reduct M).mem b D)
    (hG : MultiplicationGraph hM w D S zero mul A b W E G) (hUnit : Old zero D e unit)
    (hOld : OldIntersections w D S zero mul A W) (hGate : ExitGates w D S zero mul A W G)
    (hx : (Project.FirstOrderSemantics.reduct M).mem x W) (hy : (Project.FirstOrderSemantics.reduct M).mem y W)
    (hxs : HeadSome w D S x s) (hyt : HeadSome w D S y t) (hst : s ≠ t)
    (hzW : (Project.FirstOrderSemantics.reduct M).mem z W) (hxz : Divides W G x z) (hyz : Divides W G y z) :
    ∃ j, (Project.FirstOrderSemantics.reduct M).mem j W ∧ JoinProperty W G x y j := by
  have hmW := ConstructionProbeWordMonoid.monoid_laws hM hw hz hzw hm hAlpha hW hb hUnit hG
  by_cases hxy : Divides W G x y
  · exact ⟨y,hy,fun _ _ => ⟨And.right,fun h => ⟨divides_trans hmW hx hxy h,h⟩⟩⟩
  by_cases hyx : Divides W G y x
  · exact ⟨x,hx,fun _ _ => ⟨And.left,fun h => ⟨h,divides_trans hmW hy hyx h⟩⟩⟩
  have noS {q} (hq : (Project.FirstOrderSemantics.reduct M).mem q W) (hyq : Divides W G y q) :
      ¬ HeadSome w D S q s := fun h => hyx (dvd_of_different_head hM hw hz hGate hx hy hxs hyt hst hq hyq h)
  have noT {q} (hq : (Project.FirstOrderSemantics.reduct M).mem q W) (hxq : Divides W G x q) :
      ¬ HeadSome w D S q t := fun h => hxy (dvd_of_different_head hM hw hz hGate hy hx hyt hxs (Ne.symm hst) hq hxq h)
  obtain ⟨g,hg,hgate⟩ := hGate x s z hx hxs hzW hxz (noS hzW hyz)
  obtain ⟨k,hk,kgate⟩ := hGate y t z hy hyt hzW hyz (noT hzW hxz)
  obtain ⟨j,hj,hjoin⟩ := hOld g k z hg hk hzW ((hgate z hzW).mp ⟨hxz,noS hzW hyz⟩) ((kgate z hzW).mp ⟨hyz,noT hzW hxz⟩)
  obtain ⟨oj,hoj⟩ := exists_old hM (zero := zero) hj
  refine ⟨oj,old_word hM hz hzw hW hoj,fun q hq => ?_⟩
  apply Iff.trans ?_ ((hjoin q hq).trans (old_dvd_iff_headDiv hM hw hz hzw hm hAlpha hW hb hG hoj hq).symm)
  exact ⟨fun ⟨hxq,hyq⟩ => ⟨(hgate q hq).mp ⟨hxq,noS hq hyq⟩,(kgate q hq).mp ⟨hyq,noT hq hxq⟩⟩,
    fun ⟨hgq,hkq⟩ => ⟨((hgate q hq).mpr hgq).1,((kgate q hq).mpr hkq).1⟩⟩

/-- The original left_mul_dvd_iff, for specified products in the existing graph. -/
theorem left_mul_dvd_iff {W G unit c x y cx cy : M.Carrier .set}
    (hm : LeftCancelMonoid W G unit)
    (hc : (Project.FirstOrderSemantics.reduct M).mem c W) (hx : (Project.FirstOrderSemantics.reduct M).mem x W)
    (hy : (Project.FirstOrderSemantics.reduct M).mem y W) (hcx : Product G c x cx) (hcy : Product G c y cy) :
    Divides W G cx cy ↔ Divides W G x y := by
  constructor
  · rintro ⟨r,hr,hcr⟩
    obtain ⟨xr,hxrW,hxr⟩ := (hm.2.1 x hx).1 r hr
    have he := (hm.2.1 c hc).2.2 xr y cy hxrW hy ((hm.2.2 c x r cx xr cy hc hx hr hcx hxr).mp hcr) hcy
    exact ⟨r,hr,he ▸ hxr⟩
  · rintro ⟨r,hr,hxr⟩
    exact ⟨r,hr,(hm.2.2 c x r cx y cy hc hx hr hcx hxr).mpr hcy⟩

theorem translate_cone_intersection {W G unit c x y j cx cy cj : M.Carrier .set}
    (hm : LeftCancelMonoid W G unit)
    (hc : (Project.FirstOrderSemantics.reduct M).mem c W) (hx : (Project.FirstOrderSemantics.reduct M).mem x W)
    (hy : (Project.FirstOrderSemantics.reduct M).mem y W) (hj : (Project.FirstOrderSemantics.reduct M).mem j W)
    (hcxW : (Project.FirstOrderSemantics.reduct M).mem cx W) (hcyW : (Project.FirstOrderSemantics.reduct M).mem cy W)
    (hcx : Product G c x cx) (hcy : Product G c y cy) (hcj : Product G c j cj)
    (hjoin : JoinProperty W G x y j) : JoinProperty W G cx cy cj := by
  intro q _
  constructor
  · rintro ⟨⟨r,hr,hcxr⟩,hyq⟩
    obtain ⟨xr,hxrW,hxr⟩ := (hm.2.1 x hx).1 r hr
    have hcq := (hm.2.2 c x r cx xr q hc hx hr hcx hxr).mp hcxr
    have hyxr := (left_mul_dvd_iff hm hc hy hxrW hcy hcq).mp hyq
    exact (left_mul_dvd_iff hm hc hj hxrW hcj hcq).mpr ((hjoin xr hxrW).mp ⟨⟨r,hr,hxr⟩,hyxr⟩)
  · intro hjq
    have hxyj := (hjoin j hj).mpr ⟨unit,hm.1.1,((hm.1.2 j hj j).2).mpr rfl⟩
    exact ⟨divides_trans hm hcxW ((left_mul_dvd_iff hm hc hx hj hcx hcj).mpr hxyj.1) hjq,
      divides_trans hm hcyW ((left_mul_dvd_iff hm hc hy hj hcy hcj).mpr hxyj.2) hjq⟩

def ConeJoinAt (W G x : M.Carrier .set) : Prop :=
  (Project.FirstOrderSemantics.reduct M).mem x W → ∀ y z,
  (Project.FirstOrderSemantics.reduct M).mem y W → (Project.FirstOrderSemantics.reduct M).mem z W →
  Divides W G x z → Divides W G y z → ∃ j, (Project.FirstOrderSemantics.reduct M).mem j W ∧ JoinProperty W G x y j

def coneJoinAt {m : Nat} (W G x : Fin m) : Project.Formula 1 m :=
  .imp (.mem (.bound x) (.bound W)) (.forallE (.forallE
    (.imp (.mem (.bound 1) (.bound W.succ.succ)) (.imp (.mem (.bound 0) (.bound W.succ.succ))
      (.imp (ProjectSyntax.encode id (ConstructionBaseMonoid.divides W.succ.succ G.succ.succ x.succ.succ 0))
        (.imp (ProjectSyntax.encode id (ConstructionBaseMonoid.divides W.succ.succ G.succ.succ 1 0))
          (.existsE (.conj (.mem (.bound 0) (.bound W.succ.succ.succ))
            (joinProperty W.succ.succ.succ G.succ.succ.succ x.succ.succ.succ 2 0)))))))))

theorem coneJoinAt_freeClosed {m : Nat} (W G x : Fin m) : (coneJoinAt W G x).FreeClosed := by
  simp -implicitDefEqProofs [coneJoinAt,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,joinProperty_freeClosed]

theorem coneJoinAt_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (W G x : Fin m) :
    Project.Formula.satisfies env (coneJoinAt W G x) ↔ ConeJoinAt (env.bound W) (env.bound G) (env.bound x) := by
  simp only [coneJoinAt,ConeJoinAt,Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_mem_iff,
    Project.Term.eval_bound,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ConstructionBaseMonoid.divides_semantics (M := M),joinProperty_semantics hM]
  rfl

/-- The source Raw induction. y and the common multiple vary inside its pure schema. -/
theorem cone_join (hM : FirstOrder.Theory.Models M nativeZF)
    {w D S zero mul A b W E e I G unit : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ v, ¬ (Project.FirstOrderSemantics.reduct M).mem v zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hm : LeftCancelMonoid D mul e) (hc : Conical D mul e) (hAlpha : Alphabet D mul e S I A E)
    (hW : WordCarrier w D S mul A b W) (hb : (Project.FirstOrderSemantics.reduct M).mem b D) (hne : b ≠ e)
    (hG : MultiplicationGraph hM w D S zero mul A b W E G) (hUnit : Old zero D e unit)
    (hOld : OldIntersections w D S zero mul A W) (hGate : ExitGates w D S zero mul A W G) :
    ∀ x, Raw w D S x → ConeJoinAt W G x := by
  have hmW := ConstructionProbeWordMonoid.monoid_laws hM hw hz hzw hm hAlpha hW hb hUnit hG
  let schema : Project.UnarySchema 2 := { body := coneJoinAt 1 2 0, freeClosed := coneJoinAt_freeClosed _ _ _ }
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 2 :=
    { bound := Fin.cases W (fun _ => G), free := fun _ => w }
  have he (x) : schema.denote env x ↔ ConeJoinAt W G x := coneJoinAt_semantics hM (env.push x) 1 2 0
  have hAll : ∀ x, Raw w D S x → schema.denote env x := by
    apply ConstructionProbeEvaluationLaws.raw_induction hM env schema hw hz hzw
    · intro a x ha
      apply (he x).mpr
      intro _ y z hy hzW hxz hyz
      exact old_word_cone_join hM hw hz hzw hm hAlpha hW hb hG hUnit hOld hGate ha hy hzW hxz hyz
    · intro s t x hCons ih
      apply (he x).mpr
      intro hx y z hy hzW hxz hyz
      have hred := (ConstructionProbeReduced.reduced_cons hM hw hz hzw hCons).mp ((hW x).mp hx)
      have ht := (hW t).mpr hred.1
      rcases cases_raw hM hw hz hzw (word_raw hW hy) with ⟨a,ha⟩ | ⟨r,u,hConsY⟩
      · obtain ⟨j,hj,hjoin⟩ := old_word_cone_join hM hw hz hzw hm hAlpha hW hb hG hUnit hOld hGate ha hx hzW hyz hxz
        exact ⟨j,hj,fun q hq => and_comm.trans (hjoin q hq)⟩
      · by_cases hsr : s = r
        · subst r
          have hredY := (ConstructionProbeReduced.reduced_cons hM hw hz hzw hConsY).mp ((hW y).mp hy)
          have hu := (hW u).mpr hredY.1
          obtain ⟨c,hgen⟩ := exists_cons hM hw (cons_letter hCons) (old_raw hM hz hzw hUnit)
          have hcW := ConstructionProbeGenerator.generator_word hM hw hz hzw hc hW hb hne hUnit hgen
          have hcx := ConstructionProbeGenerator.generator_mul_of_not_headDiv hM hw hz hzw hm hAlpha hW hb hUnit hG hgen hcW ht hred.2 hCons
          have hcy := ConstructionProbeGenerator.generator_mul_of_not_headDiv hM hw hz hzw hm hAlpha hW hb hUnit hG hgen hcW hu hredY.2 hConsY
          obtain ⟨v,hv,hxv⟩ := hxz
          obtain ⟨tv,htvW,htv⟩ := (hmW.2.1 t ht).1 v hv
          have hcz := (hmW.2.2 c t v x tv z hcW ht hv hcx htv).mp hxv
          have hutv := (left_mul_dvd_iff hmW hcW hu htvW hcy hcz).mp hyz
          obtain ⟨j,hj,hjoin⟩ := (he t).mp ih ht u tv hu htvW ⟨v,hv,htv⟩ hutv
          obtain ⟨cj,hcjW,hcj⟩ := (hmW.2.1 c hcW).1 j hj
          exact ⟨cj,hcjW,translate_cone_intersection hmW hcW ht hu hj hx hy hcx hcy hcj hjoin⟩
        · exact different_head_cone_join hM hw hz hzw hm hAlpha hW hb hG hUnit hOld hGate hx hy
            ⟨t,hCons⟩ ⟨u,hConsY⟩ hsr hzW hxz hyz
  exact fun x hx => (he x).mp (hAll x hx)

/-- Path.extension_hasConditionalJoins: discharge both old intersections and gates.
The base ConditionalJoins remains the original source hypothesis; the conclusion
is ConditionalJoins on the actual extended Word carrier and multiplication. -/
theorem conditional_joins (hM : FirstOrder.Theory.Models M nativeZF)
    {w D S zero mul A b W E e I G unit O : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ v, ¬ (Project.FirstOrderSemantics.reduct M).mem v zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hm : LeftCancelMonoid D mul e) (hc : Conical D mul e) (hAlpha : Alphabet D mul e S I A E)
    (hW : WordCarrier w D S mul A b W) (hb : (Project.FirstOrderSemantics.reduct M).mem b D) (hne : b ≠ e)
    (hG : MultiplicationGraph hM w D S zero mul A b W E G) (hUnit : Old zero D e unit)
    (hO : OldGraph zero D O) (hJ : ConditionalJoins D mul) (hA : Conservative D W mul G O) : ConditionalJoins W G := by
  have hOld := old_intersections hM hw hz hzw hm hAlpha hW hb hG hO hJ hA
  have hGate := gate_existence hM hw hz hzw hm hAlpha hW hb hG hUnit hO hJ hA
  intro x y z hx hy hzW hxz hyz
  exact cone_join hM hw hz hzw hm hc hAlpha hW hb hne hG hUnit hOld hGate x (word_raw hW hx) hx y z hy hzW hxz hyz

/-- Assemble the three fields of the source extension Object on the same W/G/unit.
The old conservative embedding is constructed by the existing theorem, not a
premise of this endpoint. Source alphabet/cone interfaces remain explicit. -/
theorem extension_laws (hM : FirstOrder.Theory.Models M nativeZF)
    {w D S zero mul A b W E e I G unit node F projection : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ v, ¬ (Project.FirstOrderSemantics.reduct M).mem v zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hm : LeftCancelMonoid D mul e) (hc : Conical D mul e) (hAlpha : Alphabet D mul e S I A E)
    (hW : WordCarrier w D S mul A b W) (hb : (Project.FirstOrderSemantics.reduct M).mem b D) (hne : b ≠ e)
    (hG : MultiplicationGraph hM w D S zero mul A b W E G) (hUnit : Old zero D e unit)
    (hCone : ConstructionProbeCones.ConeLaws w D mul e zero node F S projection A)
    (hJ : ConditionalJoins D mul) : LeftCancelMonoid W G unit ∧ Conical W G unit ∧ ConditionalJoins W G := by
  obtain ⟨O,hO,_,hA⟩ := ConstructionProbeConservative.exists_conservative_old hM hw hz hzw hm hAlpha hW hb hG hUnit hCone
  exact ⟨ConstructionProbeWordMonoid.monoid_laws hM hw hz hzw hm hAlpha hW hb hUnit hG,
    ConstructionProbeOldEmbedding.word_conical hM hw hz hzw hc hAlpha hW hUnit hG,
    conditional_joins hM hw hz hzw hm hc hAlpha hW hb hne hG hUnit hO hJ hA⟩

/-- Execute the source extension using only existing carrier and function constructors. -/
theorem exists_extension (hM : FirstOrder.Theory.Models M nativeZF)
    {w D S zero mul A b E e I node F projection : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ v, ¬ (Project.FirstOrderSemantics.reduct M).mem v zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hm : LeftCancelMonoid D mul e) (hc : Conical D mul e) (hAlpha : Alphabet D mul e S I A E)
    (hb : (Project.FirstOrderSemantics.reduct M).mem b D) (hne : b ≠ e)
    (hCone : ConstructionProbeCones.ConeLaws w D mul e zero node F S projection A)
    (hJ : ConditionalJoins D mul) :
    ∃ W unit J G, WordCarrier w D S mul A b W ∧ Old zero D e unit ∧
      ConstructionProbeLetters.Representatives W W J ∧ MapsTo J W G ∧
      MultiplicationGraph hM w D S zero mul A b W E G ∧
      LeftCancelMonoid W G unit ∧ Conical W G unit ∧ ConditionalJoins W G := by
  obtain ⟨W,hW⟩ := ConstructionProbeWord.exists_word_carrier hM hw D S mul A b
  obtain ⟨unit,hUnit⟩ := exists_old hM hm.1.1 (zero := zero)
  obtain ⟨J,G,hJpairs,hG,hGraph⟩ := ConstructionProbeWordMonoid.exists_multiplication hM hw hz hzw hm hAlpha hW hb
  exact ⟨W,unit,J,G,hW,hUnit,hJpairs,hG,hGraph,
    extension_laws hM hw hz hzw hm hc hAlpha hW hb hne hGraph hUnit hCone hJ⟩

open ConstructionProbeAlphabet (alphabet alphabet_freeClosed alphabet_semantics)
open ConstructionProbeWord (wordCarrier wordCarrier_freeClosed wordCarrier_semantics)
open ConstructionProbeWordMonoidSyntax (multiplicationGraph multiplicationGraph_freeClosed multiplicationGraph_semantics)
open ConstructionProbeSharedIntersections (conditionalJoins conditionalJoins_freeClosed conditionalJoins_semantics)
open ConstructionProbeCones (coneLaws coneLaws_freeClosed coneLaws_semantics)

def extensionSentence : Project.Sentence where
  formula := Project.Formula.forallClosure 13
    (.imp (Project.Formula.isOmega (.bound (0 : Fin 13))) (.imp (Project.Formula.isEmpty (.bound (3 : Fin
    13))) (.imp (.mem (.bound (3 : Fin 13)) (.bound (0 : Fin 13))) (.imp (ProjectSyntax.encode id
    (ForcingDiagramPoset.leftCancelMonoid (1 : Fin 13) (4 : Fin 13) (8 : Fin 13))) (.imp
    (ProjectSyntax.encode id (ForcingDiagramPoset.conical (1 : Fin 13) (4 : Fin 13) (8 : Fin 13))) (.imp
    (alphabet (1 : Fin 13) (4 : Fin 13) (8 : Fin 13) (2 : Fin 13) (9 : Fin 13) (5 : Fin 13) (7 : Fin 13))
    (.imp (.mem (.bound (6 : Fin 13)) (.bound (1 : Fin 13))) (.imp (.neg (Project.Formula.extensionalEq
    (.bound (6 : Fin 13)) (.bound (8 : Fin 13)))) (.imp (coneLaws (0 : Fin 13) (1 : Fin 13) (4 : Fin 13)
    (8 : Fin 13) (3 : Fin 13) (10 : Fin 13) (11 : Fin 13) (2 : Fin 13) (12 : Fin 13) (5 : Fin 13)) (.imp
    (conditionalJoins (1 : Fin 13) (4 : Fin 13)) (.existsE (.existsE (.existsE (.existsE (.conj
    (wordCarrier (0 : Fin 13).succ.succ.succ.succ (1 : Fin 13).succ.succ.succ.succ (2 : Fin
    13).succ.succ.succ.succ (4 : Fin 13).succ.succ.succ.succ (5 : Fin 13).succ.succ.succ.succ (6 : Fin
    13).succ.succ.succ.succ 3) (.conj (old (3 : Fin 13).succ.succ.succ.succ (1 : Fin
    13).succ.succ.succ.succ (8 : Fin 13).succ.succ.succ.succ 2) (.conj
    (ConstructionProbeLetters.representatives 3 3 1) (.conj (ProjectSyntax.encode id
    (Source.SetLanguage.mapsTo 0 1 3)) (.conj (multiplicationGraph (0 : Fin 13).succ.succ.succ.succ (1 :
    Fin 13).succ.succ.succ.succ (2 : Fin 13).succ.succ.succ.succ (3 : Fin 13).succ.succ.succ.succ (4 :
    Fin 13).succ.succ.succ.succ (5 : Fin 13).succ.succ.succ.succ (6 : Fin 13).succ.succ.succ.succ 3 (7 :
    Fin 13).succ.succ.succ.succ 0) (.conj (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid
    3 0 2)) (.conj (ProjectSyntax.encode id (ForcingDiagramPoset.conical 3 0 2)) (conditionalJoins 3
    0))))))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
      Project.Formula.isEmpty,Project.Formula.extensionalEq,alphabet_freeClosed,wordCarrier_freeClosed,
      multiplicationGraph_freeClosed,old_freeClosed,coneLaws_freeClosed,conditionalJoins_freeClosed,
      ConstructionProbeLetters.representatives_freeClosed]

theorem extension_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence extensionSentence).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) extensionSentence]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_neg_iff,
    Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_isOmega_iff,Project.Formula.satisfies_isEmpty_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM),
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),ForcingDiagramPoset.conical_semantics (M := M),
    alphabet_semantics hM,wordCarrier_semantics hM,multiplicationGraph_semantics hM,old_semantics hM,
    coneLaws_semantics hM,conditionalJoins_semantics hM,ConstructionProbeLetters.representatives_semantics hM,
    ForcingSupportSize.mapsTo_semantics (M := M)]
  exact fun hw hz hzw hm hc hAlpha hb hne hCone hJ =>
    exists_extension hM hw hz hzw hm hc hAlpha hb hne hCone hJ

theorem extension_kernel_certificate : FirstOrder.Derives nativeZF []
    (Project.fo_sentence extensionSentence) := ModelTransfer.derives (fun _ hM => extension_models hM)

end PPAC.Migration.ConstructionProbeConditionalJoins
