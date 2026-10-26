/- Pinned ProbeGates generator gates, full initial-probe divisor profile and
join profile. The old profile is lifted to every Word divisor, not just old ones.
Consumers: Algebra.PersistentProfiles.Path.probeProfile and Construction.MonoidRounds. -/
import PPAC.Migration.ConstructionProbeConditionalJoins
import PPAC.Migration.ConstructionProbeIndexedGeneratorsSyntax

namespace PPAC.Migration.ConstructionProbeProfiles
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionProbeRaw ConstructionProbeRawAction ConstructionProbeGates
open ConstructionProbeWord (WordCarrier word_raw)
open ConstructionProbeOldEmbedding (OldGraph old_word old_dvd_iff_headDiv)
open ConstructionProbeWordMonoid (MultiplicationGraph)
open ConstructionProbeAlphabet (Alphabet)
open ConstructionProbeSharedIntersections (ConditionalJoins)
open ConstructionBaseMonoid (Divides)
open ForcingDiagramOrder (Product)
open ForcingDiagramPoset (LeftCancelMonoid)
open ForcingSupportSize (MapsTo)
open ForcingConditionGraphs (function_input function_unique)
open ConstructionProbeConditionalJoins (ExitGates)
open ConstructionProbePath (Path TerminalTable)
open ConstructionProbeCones (JoinProperty joinProperty joinProperty_freeClosed joinProperty_semantics)
open ForcingDiagramPoset (Conical)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

theorem generator_gate (hM : FirstOrder.Theory.Models M nativeZF)
    {w D S zero mul A b W E e I G unit s gen ex : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ v, ¬ (Project.FirstOrderSemantics.reduct M).mem v zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hm : LeftCancelMonoid D mul e) (hc : Conical D mul e) (hAlpha : Alphabet D mul e S I A E)
    (hW : WordCarrier w D S mul A b W) (hb : (Project.FirstOrderSemantics.reduct M).mem b D) (hne : b ≠ e)
    (hG : MultiplicationGraph hM w D S zero mul A b W E G) (hUnit : Old zero D e unit)
    (hgen : Cons w D S s unit gen) (hex : PureKuratowski.PairMember M s ex E) : Gate w D S zero mul A W G gen s ex := by
  have hmW := ConstructionProbeWordMonoid.monoid_laws hM hw hz hzw hm hAlpha hW hb hUnit hG
  have hexD := hAlpha.2.2.2.1.2 s ex hex
  apply gate_of_suffix_intersection hM hw hz hzw hm hAlpha hW hb hG hUnit hgen
    (old_word hM hz hzw hW hUnit) (ConstructionProbeGenerator.not_headDiv_unit hz hc hb hne hUnit)
    hm.1.1 (((hm.1.2 b hb b).2).mpr rfl) hex (((hm.1.2 ex hexD ex).2).mpr rfl)
  intro z hzW
  exact ⟨And.right,fun h => ⟨⟨z,hzW,((hmW.1.2 z hzW z).1).mpr rfl⟩,h⟩⟩

theorem generator_dvd_of_head (hM : FirstOrder.Theory.Models M nativeZF)
    {w D S zero mul A b W E e I G unit s gen q : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ v, ¬ (Project.FirstOrderSemantics.reduct M).mem v zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hm : LeftCancelMonoid D mul e) (hAlpha : Alphabet D mul e S I A E)
    (hW : WordCarrier w D S mul A b W) (hb : (Project.FirstOrderSemantics.reduct M).mem b D)
    (hG : MultiplicationGraph hM w D S zero mul A b W E G) (hUnit : Old zero D e unit)
    (hgen : Cons w D S s unit gen) (hgenW : (Project.FirstOrderSemantics.reduct M).mem gen W)
    (hq : (Project.FirstOrderSemantics.reduct M).mem q W) (hhead : HeadSome w D S q s) : Divides W G gen q := by
  obtain ⟨tail,ht,hn,hcons⟩ := (head_some_cons_iff hM hw hz hzw hW hq).mp hhead
  exact ⟨tail,ht,ConstructionProbeGenerator.generator_mul_of_not_headDiv hM hw hz hzw hm hAlpha hW hb hUnit hG hgen hgenW ht hn hcons⟩

theorem old_factor_of_other_block (hM : FirstOrder.Theory.Models M nativeZF)
    {w D S zero mul A b W E e I G unit x z s : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ v, ¬ (Project.FirstOrderSemantics.reduct M).mem v zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hm : LeftCancelMonoid D mul e) (hAlpha : Alphabet D mul e S I A E)
    (hW : WordCarrier w D S mul A b W) (hb : (Project.FirstOrderSemantics.reduct M).mem b D)
    (hG : MultiplicationGraph hM w D S zero mul A b W E G) (hUnit : Old zero D e unit)
    (hGate : ExitGates w D S zero mul A W G)
    (hx : (Project.FirstOrderSemantics.reduct M).mem x W) (hzW : (Project.FirstOrderSemantics.reduct M).mem z W)
    (hnot : ¬ HeadSome w D S x s) (hhead : HeadSome w D S z s) (hxz : Divides W G x z) :
    ∃ g og, Old zero D g og ∧ Divides W G x og ∧ Divides W G og z := by
  have hmW := ConstructionProbeWordMonoid.monoid_laws hM hw hz hzw hm hAlpha hW hb hUnit hG
  rcases cases_raw hM hw hz hzw (word_raw hW hx) with ⟨g,hg⟩ | ⟨t,Y,hCons⟩
  · exact ⟨g,x,hg,⟨unit,hmW.1.1,((hmW.1.2 x hx x).2).mpr rfl⟩,hxz⟩
  · have hExit : ¬ HeadSome w D S z t := by
      intro ht
      have hts := head_unique hM hw ht hhead
      exact hnot (hts ▸ ⟨Y,hCons⟩)
    obtain ⟨g,hg,hgate⟩ := hGate x t z hx ⟨Y,hCons⟩ hzW hxz hExit
    obtain ⟨og,hog⟩ := exists_old hM (zero := zero) hg
    have hogW := old_word hM hz hzw hW hog
    have hSelf : HeadDiv w D S zero mul A g og :=
      (headDiv_old_iff hz hog).mpr ⟨e,hm.1.1,((hm.1.2 g hg g).2).mpr rfl⟩
    exact ⟨g,og,hog,((hgate og hogW).mpr hSelf).1,
      (old_dvd_iff_headDiv hM hw hz hzw hm hAlpha hW hb hG hog hzW).mpr ((hgate z hzW).mp ⟨hxz,hExit⟩)⟩

theorem dvd_of_other_block (hM : FirstOrder.Theory.Models M nativeZF)
    {w D S zero mul A b W E e I G x y z s : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ v, ¬ (Project.FirstOrderSemantics.reduct M).mem v zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hm : LeftCancelMonoid D mul e) (hAlpha : Alphabet D mul e S I A E)
    (hW : WordCarrier w D S mul A b W) (hb : (Project.FirstOrderSemantics.reduct M).mem b D)
    (hG : MultiplicationGraph hM w D S zero mul A b W E G) (hGate : ExitGates w D S zero mul A W G)
    (hx : (Project.FirstOrderSemantics.reduct M).mem x W) (hy : (Project.FirstOrderSemantics.reduct M).mem y W)
    (hzW : (Project.FirstOrderSemantics.reduct M).mem z W) (hxs : HeadSome w D S x s)
    (hnot : ¬ HeadSome w D S y s) (hyz : Divides W G y z) (hzs : HeadSome w D S z s) : Divides W G y x := by
  rcases cases_raw hM hw hz hzw (word_raw hW hy) with ⟨a,ha⟩ | ⟨t,Y,hCons⟩
  · exact (old_dvd_iff_headDiv hM hw hz hzw hm hAlpha hW hb hG ha hx).mpr
      ((headDiv_of_same_head hM hw hz hxs hzs).mpr ((old_dvd_iff_headDiv hM hw hz hzw hm hAlpha hW hb hG ha hzW).mp hyz))
  · exact ConstructionProbeConditionalJoins.dvd_of_different_head hM hw hz hGate hx hy hxs ⟨Y,hCons⟩
      (fun hst => hnot (hst.symm ▸ ⟨Y,hCons⟩)) hzW hyz hzs

/-- Actual exit at letter(0,1): terminal(0)=a, target=1*a, exit=a*d. -/
theorem initial_exit {w D zero mul A E e node a T projection K d s ad : M.Carrier .set}
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hm : LeftCancelMonoid D mul e) (hPath : Path w D mul e zero a node)
    (hT : TerminalTable w D mul node a T)
    (hTarget : ConstructionProbeTarget.TargetLaws mul projection T A K)
    (hExit : ConstructionProbeAlphabet.ExitGraph mul K d E)
    (hzero : Product projection zero e s) (had : Product mul a d ad) : PureKuratowski.PairMember M s ad E := by
  have hTa : PureKuratowski.PairMember M zero a T :=
    (hT zero a).mpr ⟨hzw,e,hPath.2.2.1,hPath.2.1,((hm.1.2 a hPath.2.1 a).1).mpr rfl⟩
  exact (hExit s ad).mpr ⟨a,(hTarget.1 zero e a s a hzero hTa).mpr (((hm.1.2 a hPath.2.1 a).1).mpr rfl),had⟩

theorem probe_old_profile (hM : FirstOrder.Theory.Models M nativeZF)
    {w D S zero mul A b W E e I G unit s gen node F projection x ox : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ v, ¬ (Project.FirstOrderSemantics.reduct M).mem v zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hm : LeftCancelMonoid D mul e) (hAlpha : Alphabet D mul e S I A E)
    (hW : WordCarrier w D S mul A b W) (hb : (Project.FirstOrderSemantics.reduct M).mem b D)
    (hG : MultiplicationGraph hM w D S zero mul A b W E G)
    (hgen : Cons w D S s unit gen) (hgenW : (Project.FirstOrderSemantics.reduct M).mem gen W)
    (hCone : ConstructionProbeCones.ConeLaws w D mul e zero node F S projection A)
    (hzero : Product projection zero e s) (hOld : Old zero D x ox) :
    Divides W G ox gen ↔ ConstructionProbeCones.InitialProfile w D mul node x := by
  exact (old_dvd_iff_headDiv hM hw hz hzw hm hAlpha hW hb hG hOld hgenW).trans
    ((headDiv_cons_iff hM hw hz hgen).trans (hCone.2.2.2.2.2 x s hOld.1 hzero))

theorem probe_not_dvd_a (hM : FirstOrder.Theory.Models M nativeZF)
    {w D S zero mul A b W E e I G unit s gen a d ad oa : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ v, ¬ (Project.FirstOrderSemantics.reduct M).mem v zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hm : LeftCancelMonoid D mul e) (hAlpha : Alphabet D mul e S I A E)
    (hW : WordCarrier w D S mul A b W) (hb : (Project.FirstOrderSemantics.reduct M).mem b D)
    (hG : MultiplicationGraph hM w D S zero mul A b W E G)
    (hc : Conical D mul e) (hUnit : Old zero D e unit)
    (hgen : Cons w D S s unit gen) (hgenW : (Project.FirstOrderSemantics.reduct M).mem gen W)
    (hex : PureKuratowski.PairMember M s ad E) (ha : Old zero D a oa)
    (hd : (Project.FirstOrderSemantics.reduct M).mem d D) (hne : d ≠ e)
    (had : Product mul a d ad) : ¬ Divides W G gen oa := by
  intro hdiv
  obtain ⟨r,hr,har⟩ := (ConstructionProbeGenerator.generator_dvd_old_iff hM hw hz hzw hm hAlpha hW hb hUnit hG hgen hgenW hex ha).mp hdiv
  obtain ⟨dr,hdr,hdrp⟩ := (hm.2.1 d hd).1 r hr
  have hp := (hm.2.2 a d r ad dr a ha.1 hd hr had hdrp).mp har
  have heq := (hm.2.1 a ha.1).2.2 dr e a hdr hm.1.1 hp (((hm.1.2 a ha.1 a).2).mpr rfl)
  exact hne (hc d r hd hr (heq ▸ hdrp)).1

theorem head_ne_initial_of_dvd_a (hM : FirstOrder.Theory.Models M nativeZF)
    {w D S zero mul A b W E e I G unit s gen x oa : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ v, ¬ (Project.FirstOrderSemantics.reduct M).mem v zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hm : LeftCancelMonoid D mul e) (hAlpha : Alphabet D mul e S I A E)
    (hW : WordCarrier w D S mul A b W) (hb : (Project.FirstOrderSemantics.reduct M).mem b D)
    (hG : MultiplicationGraph hM w D S zero mul A b W E G)
    (hUnit : Old zero D e unit) (hgen : Cons w D S s unit gen)
    (hgenW : (Project.FirstOrderSemantics.reduct M).mem gen W)
    (hx : (Project.FirstOrderSemantics.reduct M).mem x W)
    (hnot : ¬ Divides W G gen oa) (hxa : Divides W G x oa) : ¬ HeadSome w D S x s := by
  intro hhead
  have hdiv := generator_dvd_of_head hM hw hz hzw hm hAlpha hW hb hG hUnit hgen hgenW hx hhead
  exact hnot (divides_trans
    (ConstructionProbeWordMonoid.monoid_laws hM hw hz hzw hm hAlpha hW hb hUnit hG) hgenW hdiv hxa)

/-- The union of path-node downsets, indexed by every internal natural number. -/
def NodeBelow (w D zero W G node x : M.Carrier .set) : Prop := ∃ i n on,
  (Project.FirstOrderSemantics.reduct M).mem i w ∧ PureKuratowski.PairMember M i n node ∧
  Old zero D n on ∧ Divides W G x on

theorem probe_full_profile (hM : FirstOrder.Theory.Models M nativeZF)
    {w D S zero mul A b W E e I G unit s gen node F projection a oa x : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ v, ¬ (Project.FirstOrderSemantics.reduct M).mem v zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hm : LeftCancelMonoid D mul e) (hAlpha : Alphabet D mul e S I A E)
    (hW : WordCarrier w D S mul A b W) (hb : (Project.FirstOrderSemantics.reduct M).mem b D)
    (hG : MultiplicationGraph hM w D S zero mul A b W E G)
    (hUnit : Old zero D e unit) (hgen : Cons w D S s unit gen)
    (hgenW : (Project.FirstOrderSemantics.reduct M).mem gen W)
    (hGate : ExitGates w D S zero mul A W G)
    (hCone : ConstructionProbeCones.ConeLaws w D mul e zero node F S projection A)
    (hPath : Path w D mul e zero a node) (hzero : Product projection zero e s)
    (ha : Old zero D a oa) (hnot : ¬ Divides W G gen oa)
    (hx : (Project.FirstOrderSemantics.reduct M).mem x W) :
    (Divides W G x gen ∧ Divides W G x oa) ↔ NodeBelow w D zero W G node x := by
  have hmW := ConstructionProbeWordMonoid.monoid_laws hM hw hz hzw hm hAlpha hW hb hUnit hG
  constructor
  · rintro ⟨hxp,hxa⟩
    have hn := head_ne_initial_of_dvd_a hM hw hz hzw hm hAlpha hW hb hG hUnit hgen hgenW hx hnot hxa
    obtain ⟨g,og,hog,hxg,hgp⟩ := old_factor_of_other_block hM hw hz hzw hm hAlpha hW hb hG hUnit hGate hx hgenW hn ⟨unit,hgen⟩ hxp
    obtain ⟨i,n,hi,hin,hgn⟩ := (probe_old_profile hM hw hz hzw hm hAlpha hW hb hG hgen hgenW hCone hzero hog).mp hgp
    obtain ⟨on,hon⟩ := exists_old hM (zero := zero) (hPath.1.2 i n hin)
    exact ⟨i,n,on,hi,hin,hon,divides_trans hmW hx hxg
      ((ConstructionProbeOldEmbedding.old_dvd_old_iff hM hw hz hzw hm hAlpha hW hb hG hog hon).mpr hgn)⟩
  · rintro ⟨i,n,on,hi,hin,hon,hxon⟩
    have honp := (probe_old_profile hM hw hz hzw hm hAlpha hW hb hG hgen hgenW hCone hzero hon).mpr
      ⟨i,n,hi,hin,e,hm.1.1,((hm.1.2 n hon.1 n).2).mpr rfl⟩
    obtain ⟨t,n',hin',ht,hnt⟩ := hPath.2.2.2.2 i hi
    have heq := function_unique hPath.1.1 hin' hin
    subst n'
    have hona := (ConstructionProbeOldEmbedding.old_dvd_old_iff hM hw hz hzw hm hAlpha hW hb hG hon ha).mpr ⟨t,ht,hnt⟩
    exact ⟨divides_trans hmW hx hxon honp,
      divides_trans hmW hx hxon hona⟩

theorem probe_join_profile (hM : FirstOrder.Theory.Models M nativeZF)
    {w D S zero mul A b W E e I G unit s gen a d ad oa oad x : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ v, ¬ (Project.FirstOrderSemantics.reduct M).mem v zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hm : LeftCancelMonoid D mul e) (hAlpha : Alphabet D mul e S I A E)
    (hW : WordCarrier w D S mul A b W) (hb : (Project.FirstOrderSemantics.reduct M).mem b D)
    (hG : MultiplicationGraph hM w D S zero mul A b W E G)
    (hc : Conical D mul e) (hbne : b ≠ e) (hUnit : Old zero D e unit)
    (hgen : Cons w D S s unit gen) (hgenW : (Project.FirstOrderSemantics.reduct M).mem gen W)
    (hex : PureKuratowski.PairMember M s ad E) (ha : Old zero D a oa) (hadOld : Old zero D ad oad)
    (hd : (Project.FirstOrderSemantics.reduct M).mem d D) (had : Product mul a d ad)
    (hGate : ExitGates w D S zero mul A W G) (hnot : ¬ Divides W G gen oa)
    (hx : (Project.FirstOrderSemantics.reduct M).mem x W)
    (hxa : Divides W G x oa) (hxp : ¬ Divides W G x gen) : JoinProperty W G x gen oad := by
  have hmW := ConstructionProbeWordMonoid.monoid_laws hM hw hz hzw hm hAlpha hW hb hUnit hG
  have hg := generator_gate hM hw hz hzw hm hc hAlpha hW hb hbne hG hUnit hgen hex
  have hxad := divides_trans hmW hx hxa
    ((ConstructionProbeOldEmbedding.old_dvd_old_iff hM hw hz hzw hm hAlpha hW hb hG ha hadOld).mpr ⟨d,hd,had⟩)
  intro z hzW
  constructor
  · rintro ⟨hxz,hpz⟩
    apply (old_dvd_iff_headDiv hM hw hz hzw hm hAlpha hW hb hG hadOld hzW).mpr
    apply (hg z hzW).mp
    refine ⟨hpz,fun hhead => hxp ?_⟩
    exact dvd_of_other_block hM hw hz hzw hm hAlpha hW hb hG hGate hgenW hx hzW ⟨unit,hgen⟩
      (head_ne_initial_of_dvd_a hM hw hz hzw hm hAlpha hW hb hG hUnit hgen hgenW hx hnot hxa) hxz hhead
  · intro hadz
    have hadW := old_word hM hz hzw hW hadOld
    have hself : HeadDiv w D S zero mul A ad oad :=
      (headDiv_old_iff hz hadOld).mpr ⟨e,hm.1.1,((hm.1.2 ad hadOld.1 ad).2).mpr rfl⟩
    exact ⟨divides_trans hmW hx hxad hadz,
      divides_trans hmW hgenW ((hg oad hadW).mpr hself).1 hadz⟩

/-- Source ProbeProfile fields in the actual extension; all divisors range over W. -/
def ProfileLaws (w D zero W G node gen oa ob oad : M.Carrier .set) : Prop :=
  Product G gen ob oad ∧ ¬ Divides W G gen oa ∧
  (∀ x, (Project.FirstOrderSemantics.reduct M).mem x W →
    ((Divides W G x gen ∧ Divides W G x oa) ↔ NodeBelow w D zero W G node x)) ∧
  (∀ x, (Project.FirstOrderSemantics.reduct M).mem x W → Divides W G x oa →
    ¬ Divides W G x gen → JoinProperty W G x gen oad)

/-- Build the same actual Word/probe system before proving its full initial profile.
No profile, old embedding, gate, or Word carrier is assumed by this endpoint. -/
theorem exists_profile_extension (hM : FirstOrder.Theory.Models M nativeZF)
    {w D S zero mul A b E e I node F projection C a d T KT : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ v, ¬ (Project.FirstOrderSemantics.reduct M).mem v zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hm : LeftCancelMonoid D mul e) (hc : Conical D mul e) (hAlpha : Alphabet D mul e S I A E)
    (hb : (Project.FirstOrderSemantics.reduct M).mem b D) (hbne : b ≠ e)
    (hCone : ConstructionProbeCones.ConeLaws w D mul e zero node F S projection A)
    (hJ : ConditionalJoins D mul) (hPath : Path w D mul e zero a node)
    (hC : ConstructionProbeLetters.Representatives w D C) (hp : MapsTo C S projection)
    (hT : TerminalTable w D mul node a T)
    (hTarget : ConstructionProbeTarget.TargetLaws mul projection T A KT)
    (hExit : ConstructionProbeAlphabet.ExitGraph mul KT d E)
    (hd : (Project.FirstOrderSemantics.reduct M).mem d D) (hdne : d ≠ e) :
    ∃ W unit J G KG P gen oa ad oad ob,
      WordCarrier w D S mul A b W ∧ Old zero D e unit ∧
      ConstructionProbeLetters.Representatives W W J ∧ MapsTo J W G ∧
      MultiplicationGraph hM w D S zero mul A b W E G ∧
      LeftCancelMonoid W G unit ∧ Conical W G unit ∧ ConditionalJoins W G ∧
      MapsTo S W KG ∧ ConstructionProbeGenerator.GeneratorGraph w D S unit KG ∧
      MapsTo w W P ∧ ConstructionProbeIndexedGenerators.ProbeGraph w projection e KG P ∧
      PureKuratowski.PairMember M zero gen P ∧ Old zero D a oa ∧ Product mul a d ad ∧
      Old zero D ad oad ∧ Old zero D b ob ∧ ProfileLaws w D zero W G node gen oa ob oad := by
  obtain ⟨W,unit,J,G,hW,hUnit,hWW,hGmap,hG,hmW,hcW,hJW⟩ :=
    ConstructionProbeConditionalJoins.exists_extension hM hw hz hzw hm hc hAlpha hb hbne hCone hJ
  obtain ⟨KG,hKG,hGen⟩ := ConstructionProbeGenerator.exists_generator_graph hM hw hz hzw hc hW hb hbne hUnit
  obtain ⟨P,hP,hProbe⟩ := ConstructionProbeIndexedGenerators.exists_probe_graph hM hC hp hm.1.1 hKG
  obtain ⟨gen,hp0,_⟩ := hP.1.2 zero hzw
  obtain ⟨_,s,hzero,hsg⟩ := (hProbe zero gen).mp hp0
  have hgen := (hGen s gen).mp hsg
  have hgenW := hP.2 zero gen hp0
  obtain ⟨ad,hadD,had⟩ := (hm.2.1 a hPath.2.1).1 d hd
  obtain ⟨oa,ha⟩ := exists_old hM (zero := zero) hPath.2.1
  obtain ⟨oad,hadOld⟩ := exists_old hM (zero := zero) hadD
  obtain ⟨ob,hob⟩ := exists_old hM (zero := zero) hb
  have hex := initial_exit hzw hm hPath hT hTarget hExit hzero had
  have hnot := probe_not_dvd_a hM hw hz hzw hm hAlpha hW hb hG hc hUnit hgen hgenW hex ha hd hdne had
  obtain ⟨O,hO,_,hConservative⟩ := ConstructionProbeConservative.exists_conservative_old hM hw hz hzw hm hAlpha hW hb hG hUnit hCone
  have hGate := ConstructionProbeConditionalJoins.gate_existence hM hw hz hzw hm hAlpha hW hb hG hUnit hO hJ hConservative
  refine ⟨W,unit,J,G,KG,P,gen,oa,ad,oad,ob,hW,hUnit,hWW,hGmap,hG,hmW,hcW,hJW,hKG,hGen,hP,hProbe,hp0,ha,had,hadOld,hob,?_,hnot,?_,?_⟩
  · exact ConstructionProbeGenerator.generator_mul_b hM hw hz hzw hm hAlpha hW hb hUnit hG hgen hgenW hex hob hadOld
  · intro x hx
    exact probe_full_profile hM hw hz hzw hm hAlpha hW hb hG hUnit hgen hgenW hGate hCone hPath hzero ha hnot hx
  · intro x hx hxa hxp
    exact probe_join_profile hM hw hz hzw hm hAlpha hW hb hG hc hbne hUnit hgen hgenW hex ha hadOld hd had hGate hnot hx hxa hxp

def nodeBelow {m : Nat} (w D zero W G node x : Fin m) : Project.Formula 1 m :=
  (.existsE (.existsE (.existsE (.conj (.mem (.bound 2) (.bound w.succ.succ.succ)) (.conj
    (ProjectSyntax.encode id (Source.SetLanguage.edge node.succ.succ.succ 2 1)) (.conj (old
    zero.succ.succ.succ D.succ.succ.succ 1 0) (ProjectSyntax.encode id (ConstructionBaseMonoid.divides
    W.succ.succ.succ G.succ.succ.succ x.succ.succ.succ 0))))))))

theorem nodeBelow_freeClosed {m : Nat} (w D zero W G node x : Fin m) : (nodeBelow w D zero W G node x).FreeClosed := by
  simp -implicitDefEqProofs [nodeBelow,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,old_freeClosed]

theorem nodeBelow_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w D zero W G node x : Fin m) :
    Project.Formula.satisfies env (nodeBelow w D zero W G node x) ↔
      NodeBelow (env.bound w) (env.bound D) (env.bound zero) (env.bound W) (env.bound G) (env.bound node) (env.bound x) := by
  simp only [nodeBelow,NodeBelow,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,
    old_semantics hM,ConstructionBaseMonoid.divides_semantics (M := M)]
  rfl

def profileLaws {m : Nat} (w D zero W G node gen oa ob oad : Fin m) : Project.Formula 1 m :=
  (.conj (ProjectSyntax.encode id (ForcingDiagramOrder.product G gen ob oad)) (.conj (.neg
    (ProjectSyntax.encode id (ConstructionBaseMonoid.divides W G gen oa))) (.conj (.forallE (.imp (.mem
    (.bound 0) (.bound W.succ)) (.iff (.conj (ProjectSyntax.encode id (ConstructionBaseMonoid.divides
    W.succ G.succ 0 gen.succ)) (ProjectSyntax.encode id (ConstructionBaseMonoid.divides W.succ G.succ 0
    oa.succ))) (nodeBelow w.succ D.succ zero.succ W.succ G.succ node.succ 0)))) (.forallE (.imp (.mem
    (.bound 0) (.bound W.succ)) (.imp (ProjectSyntax.encode id (ConstructionBaseMonoid.divides W.succ
    G.succ 0 oa.succ)) (.imp (.neg (ProjectSyntax.encode id (ConstructionBaseMonoid.divides W.succ G.succ
    0 gen.succ))) (joinProperty W.succ G.succ 0 gen.succ oad.succ))))))))

theorem profileLaws_freeClosed {m : Nat} (w D zero W G node gen oa ob oad : Fin m) :
    (profileLaws w D zero W G node gen oa ob oad).FreeClosed := by
  simp -implicitDefEqProofs [profileLaws,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,nodeBelow_freeClosed,joinProperty_freeClosed]

theorem profileLaws_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w D zero W G node gen oa ob oad : Fin m) :
    Project.Formula.satisfies env (profileLaws w D zero W G node gen oa ob oad) ↔
      ProfileLaws (env.bound w) (env.bound D) (env.bound zero) (env.bound W) (env.bound G) (env.bound node)
        (env.bound gen) (env.bound oa) (env.bound ob) (env.bound oad) := by
  simp only [profileLaws,ProfileLaws,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_neg_iff,
    Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_iff_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingDiagramOrder.product_semantics (M := M),ConstructionBaseMonoid.divides_semantics (M := M),
    nodeBelow_semantics hM,joinProperty_semantics hM]
  rfl

def profileSentence : Project.Sentence where
  formula := Project.Formula.forallClosure 18
    (.imp (Project.Formula.isOmega (.bound (0 : Fin 18))) (.imp (Project.Formula.isEmpty (.bound (3 : Fin
    18))) (.imp (.mem (.bound (3 : Fin 18)) (.bound (0 : Fin 18))) (.imp (ProjectSyntax.encode id
    (ForcingDiagramPoset.leftCancelMonoid (1 : Fin 18) (4 : Fin 18) (8 : Fin 18))) (.imp
    (ProjectSyntax.encode id (ForcingDiagramPoset.conical (1 : Fin 18) (4 : Fin 18) (8 : Fin 18))) (.imp
    (ConstructionProbeAlphabet.alphabet (1 : Fin 18) (4 : Fin 18) (8 : Fin 18) (2 : Fin 18) (9 : Fin 18)
    (5 : Fin 18) (7 : Fin 18)) (.imp (.mem (.bound (6 : Fin 18)) (.bound (1 : Fin 18))) (.imp (.neg
    (Project.Formula.extensionalEq (.bound (6 : Fin 18)) (.bound (8 : Fin 18)))) (.imp
    (ConstructionProbeCones.coneLaws (0 : Fin 18) (1 : Fin 18) (4 : Fin 18) (8 : Fin 18) (3 : Fin 18) (10
    : Fin 18) (11 : Fin 18) (2 : Fin 18) (12 : Fin 18) (5 : Fin 18)) (.imp
    (ConstructionProbeSharedIntersections.conditionalJoins (1 : Fin 18) (4 : Fin 18)) (.imp
    (ConstructionProbePath.path (0 : Fin 18) (1 : Fin 18) (4 : Fin 18) (8 : Fin 18) (3 : Fin 18) (14 :
    Fin 18) (10 : Fin 18)) (.imp (ConstructionProbeLetters.representatives (0 : Fin 18) (1 : Fin 18) (13
    : Fin 18)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (12 : Fin 18) (13 : Fin 18) (2 :
    Fin 18))) (.imp (ConstructionProbePath.terminalTable (0 : Fin 18) (1 : Fin 18) (4 : Fin 18) (10 : Fin
    18) (14 : Fin 18) (16 : Fin 18)) (.imp (ConstructionProbeTarget.targetLaws (4 : Fin 18) (12 : Fin 18)
    (16 : Fin 18) (5 : Fin 18) (17 : Fin 18)) (.imp (ConstructionProbeAlphabet.exitGraph (4 : Fin 18) (17
    : Fin 18) (15 : Fin 18) (7 : Fin 18)) (.imp (.mem (.bound (15 : Fin 18)) (.bound (1 : Fin 18))) (.imp
    (.neg (Project.Formula.extensionalEq (.bound (15 : Fin 18)) (.bound (8 : Fin 18)))) (.existsE
    (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE
    (.conj (ConstructionProbeWord.wordCarrier (11 : Fin 29) (12 : Fin 29) (13 : Fin 29) (15 : Fin 29) (16
    : Fin 29) (17 : Fin 29) (10 : Fin 29)) (.conj (old (14 : Fin 29) (12 : Fin 29) (19 : Fin 29) (9 : Fin
    29)) (.conj (ConstructionProbeLetters.representatives (10 : Fin 29) (10 : Fin 29) (8 : Fin 29))
    (.conj (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (7 : Fin 29) (8 : Fin 29) (10 : Fin 29)))
    (.conj (ConstructionProbeWordMonoidSyntax.multiplicationGraph (11 : Fin 29) (12 : Fin 29) (13 : Fin
    29) (14 : Fin 29) (15 : Fin 29) (16 : Fin 29) (17 : Fin 29) (10 : Fin 29) (18 : Fin 29) (7 : Fin 29))
    (.conj (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid (10 : Fin 29) (7 : Fin 29) (9 :
    Fin 29))) (.conj (ProjectSyntax.encode id (ForcingDiagramPoset.conical (10 : Fin 29) (7 : Fin 29) (9
    : Fin 29))) (.conj (ConstructionProbeSharedIntersections.conditionalJoins (10 : Fin 29) (7 : Fin 29))
    (.conj (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (6 : Fin 29) (13 : Fin 29) (10 : Fin 29)))
    (.conj (ConstructionProbeGeneratorSyntax.generatorGraph (11 : Fin 29) (12 : Fin 29) (13 : Fin 29) (9
    : Fin 29) (6 : Fin 29)) (.conj (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (5 : Fin 29) (11 :
    Fin 29) (10 : Fin 29))) (.conj (ConstructionProbeIndexedGeneratorsSyntax.probeGraph (11 : Fin 29) (23
    : Fin 29) (19 : Fin 29) (6 : Fin 29) (5 : Fin 29)) (.conj (ProjectSyntax.encode id
    (Source.SetLanguage.edge (5 : Fin 29) (14 : Fin 29) (4 : Fin 29))) (.conj (old (14 : Fin 29) (12 :
    Fin 29) (25 : Fin 29) (3 : Fin 29)) (.conj (ProjectSyntax.encode id (ForcingDiagramOrder.product (15
    : Fin 29) (25 : Fin 29) (26 : Fin 29) (2 : Fin 29))) (.conj (old (14 : Fin 29) (12 : Fin 29) (2 : Fin
    29) (1 : Fin 29)) (.conj (old (14 : Fin 29) (12 : Fin 29) (17 : Fin 29) (0 : Fin 29)) (profileLaws
    (11 : Fin 29) (12 : Fin 29) (14 : Fin 29) (10 : Fin 29) (7 : Fin 29) (21 : Fin 29) (4 : Fin 29) (3 :
    Fin 29) (0 : Fin 29) (1 : Fin 29))))))))))))))))))))))))))))))))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
      Project.Formula.isEmpty,Project.Formula.extensionalEq,
      ConstructionProbeAlphabet.alphabet_freeClosed,
      ConstructionProbeCones.coneLaws_freeClosed,
      ConstructionProbeSharedIntersections.conditionalJoins_freeClosed,
      ConstructionProbePath.path_freeClosed,
      ConstructionProbeLetters.representatives_freeClosed,
      ConstructionProbePath.terminalTable_freeClosed,
      ConstructionProbeTarget.targetLaws_freeClosed,
      ConstructionProbeAlphabet.exitGraph_freeClosed,
      ConstructionProbeWord.wordCarrier_freeClosed,
      old_freeClosed,
      ConstructionProbeWordMonoidSyntax.multiplicationGraph_freeClosed,
      ConstructionProbeGeneratorSyntax.generatorGraph_freeClosed,
      ConstructionProbeIndexedGeneratorsSyntax.probeGraph_freeClosed,
      profileLaws_freeClosed]

theorem profile_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence profileSentence).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) profileSentence]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_neg_iff,
    Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_isOmega_iff,Project.Formula.satisfies_isEmpty_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM),
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),ForcingDiagramPoset.conical_semantics (M := M),
    ForcingSupportSize.mapsTo_semantics (M := M),ForcingDiagramOrder.product_semantics (M := M),KuratowskiZF.source_edge,
    ConstructionProbeAlphabet.alphabet_semantics hM,
    ConstructionProbeCones.coneLaws_semantics hM,
    ConstructionProbeSharedIntersections.conditionalJoins_semantics hM,
    ConstructionProbePath.path_semantics hM,
    ConstructionProbeLetters.representatives_semantics hM,
    ConstructionProbePath.terminalTable_semantics hM,
    ConstructionProbeTarget.targetLaws_semantics hM,
    ConstructionProbeAlphabet.exitGraph_semantics hM,
    ConstructionProbeWord.wordCarrier_semantics hM,
    old_semantics hM,
    ConstructionProbeWordMonoidSyntax.multiplicationGraph_semantics hM,
    ConstructionProbeGeneratorSyntax.generatorGraph_semantics hM,
    ConstructionProbeIndexedGeneratorsSyntax.probeGraph_semantics hM,
    profileLaws_semantics hM]
  exact fun hw hz hzw hm hc hAlpha hb hbne hCone hJ hPath hC hp hT hTarget hExit hd hdne =>
    exists_profile_extension hM hw hz hzw hm hc hAlpha hb hbne hCone hJ hPath hC hp hT hTarget hExit hd hdne

theorem profile_kernel_certificate : FirstOrder.Derives nativeZF []
    (Project.fo_sentence profileSentence) := ModelTransfer.derives (fun _ hM => profile_models hM)

end PPAC.Migration.ConstructionProbeProfiles
