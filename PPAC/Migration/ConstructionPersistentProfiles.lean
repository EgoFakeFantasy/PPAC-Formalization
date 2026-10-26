/- Pinned PersistentProfiles.OldGate/HasOldGates, ProbeProfile.map and
Path.hasOldGates/preserve_profile. Consumers: MonoidBase probe profile and
successor/limit profile persistence. All carriers and path indices are internal. -/
import PPAC.Migration.ConstructionProbeProfiles
import PPAC.Migration.ConstructionProbeConservativeSyntax
import PPAC.Migration.ConstructionProbeMappedPathSyntax

namespace PPAC.Migration.ConstructionPersistentProfiles
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionProbeRaw ConstructionProbeRawAction ConstructionProbeGates
open ConstructionProbeWord (WordCarrier word_raw)
open ConstructionProbeOldEmbedding (OldGraph old_word old_dvd_iff_headDiv)
open ConstructionProbeWordMonoid (MultiplicationGraph)
open ConstructionProbeAlphabet (Alphabet)
open ConstructionProbeConservative (Conservative)
open ConstructionProbeSharedIntersections (ConditionalJoins)
open ConstructionProbeLiftHom (PreservesProducts)
open ConstructionProbeMappedPath (NodeMap exists_node_map)
open ConstructionProbeCones (InitialProfile JoinProperty)
open ConstructionBaseMonoid (Divides)
open ForcingDiagramOrder (Product)
open ForcingDiagramPoset (LeftCancelMonoid Conical)
open ForcingSupportSize (MapsTo)
open ForcingConditionGraphs (function_input function_unique)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

/-- fg is the actual f-image of g, not an independently chosen gate value. -/
def OldGate (D N mul mulN f q g fg : M.Carrier .set) : Prop :=
  PureKuratowski.PairMember M g fg f ∧ Divides N mulN q fg ∧
  (∀ x fx, PureKuratowski.PairMember M x fx f → (Divides N mulN q fx ↔ Divides D mul g x)) ∧
  (∀ x fx, PureKuratowski.PairMember M x fx f → ¬ Divides N mulN fx q →
    ∀ z, (Project.FirstOrderSemantics.reduct M).mem z N →
      ((Divides N mulN q z ∧ Divides N mulN fx z) ↔ (Divides N mulN fg z ∧ Divides N mulN fx z)))

def HasOldGates (D N mul mulN f : M.Carrier .set) : Prop := ∀ q,
  (Project.FirstOrderSemantics.reduct M).mem q N →
  (∃ a fa, PureKuratowski.PairMember M a fa f ∧ Divides N mulN q fa) →
    (∃ x, PureKuratowski.PairMember M x q f) ∨ ∃ g fg, OldGate D N mul mulN f q g fg

/-- Source ProbeProfile with carrier membership and the actual internal node graph.
The witness ad records a*d in the same multiplication graph as p*b. -/
def ProbeProfile (w D mul a b d p node : M.Carrier .set) : Prop :=
  (Project.FirstOrderSemantics.reduct M).mem a D ∧ (Project.FirstOrderSemantics.reduct M).mem b D ∧
  (Project.FirstOrderSemantics.reduct M).mem d D ∧ (Project.FirstOrderSemantics.reduct M).mem p D ∧
  MapsTo w D node ∧ ∃ ad, (Project.FirstOrderSemantics.reduct M).mem ad D ∧
    Product mul a d ad ∧ Product mul p b ad ∧ ¬ Divides D mul p a ∧
    (∀ x, (Project.FirstOrderSemantics.reduct M).mem x D →
      ((Divides D mul x a ∧ Divides D mul x p) ↔ InitialProfile w D mul node x)) ∧
    (∀ x, (Project.FirstOrderSemantics.reduct M).mem x D → Divides D mul x a →
      ¬ Divides D mul x p → JoinProperty D mul x p ad)

/-- Source Path.hasOldGates. Existing exit gates supply all three OldGate fields. -/
theorem probe_has_old_gates (hM : FirstOrder.Theory.Models M nativeZF)
    {w D S zero mul A b W E e I G unit O : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ v, ¬ (Project.FirstOrderSemantics.reduct M).mem v zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hm : LeftCancelMonoid D mul e) (hAlpha : Alphabet D mul e S I A E)
    (hW : WordCarrier w D S mul A b W) (hb : (Project.FirstOrderSemantics.reduct M).mem b D)
    (hG : MultiplicationGraph hM w D S zero mul A b W E G) (hUnit : Old zero D e unit)
    (hO : OldGraph zero D O) (hJ : ConditionalJoins D mul) (hCon : Conservative D W mul G O) :
    HasOldGates D W mul G O := by
  have gates := ConstructionProbeConditionalJoins.gate_existence hM hw hz hzw hm hAlpha hW hb hG hUnit hO hJ hCon
  intro q hq hmultiple
  rcases cases_raw hM hw hz hzw (word_raw hW hq) with ⟨a,ha⟩ | ⟨s,t,hcons⟩
  · exact Or.inl ⟨a,(hO a q).mpr ha⟩
  · obtain ⟨a,fa,hfa,hqfa⟩ := hmultiple
    have hfaOld := (hO a fa).mp hfa
    obtain ⟨g,hg,hgate⟩ := gates q s fa hq ⟨t,hcons⟩ (old_word hM hz hzw hW hfaOld) hqfa (old_no_head hz hfaOld)
    obtain ⟨fg,hfg⟩ := exists_old hM (zero := zero) hg
    have hfgW := old_word hM hz hzw hW hfg
    refine Or.inr ⟨g,fg,(hO g fg).mpr hfg,?_,?_,?_⟩
    · exact (gate_dvd_old_iff hz hgate hfg hfgW).mpr ⟨e,hm.1.1,((hm.1.2 g hg g).2).mpr rfl⟩
    · intro x fx hfx
      exact gate_dvd_old_iff hz hgate ((hO x fx).mp hfx) (hCon.1.1.2 x fx hfx)
    · intro x fx hfx hnot z hzW
      have hxOld := (hO x fx).mp hfx
      have hxq := old_dvd_iff_headDiv hM hw hz hzw hm hAlpha hW hb hG hxOld hq
      have hi := gate_old_intersection hM hw hz hgate ⟨t,hcons⟩ (fun h => hnot (hxq.mpr h)) hzW
      have hxz := old_dvd_iff_headDiv hM hw hz hzw hm hAlpha hW hb hG hxOld hzW
      have hgz := old_dvd_iff_headDiv hM hw hz hzw hm hAlpha hW hb hG hfg hzW
      exact ⟨fun ⟨hqz,hxz'⟩ => let h := hi.mp ⟨hxz.mp hxz',hqz⟩; ⟨hgz.mpr h.2,hxz.mpr h.1⟩,
        fun ⟨hgz',hxz'⟩ => let h := hi.mpr ⟨hxz.mp hxz',hgz.mp hgz'⟩; ⟨h.2,hxz.mpr h.1⟩⟩

/-- The exact source old-image / old-gate alternatives, on the whole new carrier.
LeftCancelMonoid is the existing Object contract used by all current consumers. -/
theorem map_profile {w D N mul mulN e eN f a b d p node mapped fa fb fd fp : M.Carrier .set}
    (hm : LeftCancelMonoid D mul e) (hmN : LeftCancelMonoid N mulN eN)
    (hCon : Conservative D N mul mulN f) (hPres : PreservesProducts mul mulN f)
    (hGates : HasOldGates D N mul mulN f) (hProfile : ProbeProfile w D mul a b d p node)
    (hMap : NodeMap node f mapped) (hMapped : MapsTo w N mapped)
    (ha : PureKuratowski.PairMember M a fa f) (hb : PureKuratowski.PairMember M b fb f)
    (hd : PureKuratowski.PairMember M d fd f) (hp : PureKuratowski.PairMember M p fp f) :
    ProbeProfile w N mulN fa fb fd fp mapped := by
  have hf := hCon.1.1
  have hReflect := ConstructionProbeAlphabetMap.division_reflection hm hmN hCon.1 hPres hCon.2.1
  obtain ⟨_,_,_,_,hn,ad,hadD,had,hpb,hnot,hdiv,hjoin⟩ := hProfile
  obtain ⟨fad,hfad,_⟩ := hf.1.2 ad hadD
  refine ⟨hf.2 a fa ha,hf.2 b fb hb,hf.2 d fd hd,hf.2 p fp hp,hMapped,
    fad,hf.2 ad fad hfad,hPres a d ad fa fd fad had ha hd hfad,
    hPres p b ad fp fb fad hpb hp hb hfad,fun h => hnot ((hReflect p a fp fa hp ha).mp h),?_,?_⟩
  · intro x hx
    constructor
    · rintro ⟨hxa,hxp⟩
      rcases hGates x hx ⟨a,fa,ha,hxa⟩ with ⟨y,hy⟩ | ⟨g,fg,hfg,hxfg,hold,_⟩
      · obtain ⟨i,n,hi,hin,hyn⟩ := (hdiv y (function_input hf.1 hy)).mp
          ⟨(hReflect y a x fa hy ha).mp hxa,(hReflect y p x fp hy hp).mp hxp⟩
        obtain ⟨fn,hfn,_⟩ := hf.1.2 n (hn.2 i n hin)
        exact ⟨i,fn,hi,(hMap i fn).mpr ⟨n,hin,hfn⟩,(hReflect y n x fn hy hfn).mpr hyn⟩
      · obtain ⟨i,n,hi,hin,hgn⟩ := (hdiv g (function_input hf.1 hfg)).mp ⟨(hold a fa ha).mp hxa,(hold p fp hp).mp hxp⟩
        obtain ⟨fn,hfn,_⟩ := hf.1.2 n (hn.2 i n hin)
        exact ⟨i,fn,hi,(hMap i fn).mpr ⟨n,hin,hfn⟩,
          divides_trans hmN hx hxfg ((hReflect g n fg fn hfg hfn).mpr hgn)⟩
    · rintro ⟨i,fn,hi,hin,hxfn⟩
      obtain ⟨n,hin,hfn⟩ := (hMap i fn).mp hin
      have hnD := hn.2 i n hin
      have hnprof := (hdiv n hnD).mpr ⟨i,n,hi,hin,e,hm.1.1,((hm.1.2 n hnD n).2).mpr rfl⟩
      exact ⟨divides_trans hmN hx hxfn ((hReflect n a fn fa hfn ha).mpr hnprof.1),
        divides_trans hmN hx hxfn ((hReflect n p fn fp hfn hp).mpr hnprof.2)⟩
  · intro x hx hxa hxp
    rcases hGates x hx ⟨a,fa,ha,hxa⟩ with ⟨y,hy⟩ | ⟨g,fg,hfg,hxfg,hOld,hInter⟩
    · exact hCon.2.2.1 y p ad x fp fad hy hp hfad
        (hjoin y (function_input hf.1 hy) ((hReflect y a x fa hy ha).mp hxa)
          (fun h => hxp ((hReflect y p x fp hy hp).mpr h)))
    · have hga := (hOld a fa ha).mp hxa
      have hgp : ¬ Divides D mul g p := fun h => hxp ((hOld p fp hp).mpr h)
      have hpx : ¬ Divides N mulN fp x := fun h => hnot
        ((hReflect p a fp fa hp ha).mp (divides_trans hmN (hf.2 p fp hp) h hxa))
      have hj := hCon.2.2.1 g p ad fg fp fad hfg hp hfad (hjoin g (function_input hf.1 hfg) hga hgp)
      exact fun z hzN => (hInter p fp hp hpx z hzN).trans (hj z hzN)

/-- Native composition constructs f∘node; actual function values are also constructed. -/
theorem exists_mapped_profile (hM : FirstOrder.Theory.Models M nativeZF)
    {w D N mul mulN e eN f a b d p node : M.Carrier .set}
    (hm : LeftCancelMonoid D mul e) (hmN : LeftCancelMonoid N mulN eN)
    (hCon : Conservative D N mul mulN f) (hPres : PreservesProducts mul mulN f)
    (hGates : HasOldGates D N mul mulN f) (hProfile : ProbeProfile w D mul a b d p node) :
    ∃ mapped fa fb fd fp, NodeMap node f mapped ∧
      PureKuratowski.PairMember M a fa f ∧ PureKuratowski.PairMember M b fb f ∧
      PureKuratowski.PairMember M d fd f ∧ PureKuratowski.PairMember M p fp f ∧
      ProbeProfile w N mulN fa fb fd fp mapped := by
  obtain ⟨mapped,hMapped,hMap⟩ := exists_node_map hM hProfile.2.2.2.2.1 hCon.1.1
  obtain ⟨fa,ha,_⟩ := hCon.1.1.1.2 a hProfile.1
  obtain ⟨fb,hb,_⟩ := hCon.1.1.1.2 b hProfile.2.1
  obtain ⟨fd,hd,_⟩ := hCon.1.1.1.2 d hProfile.2.2.1
  obtain ⟨fp,hp,_⟩ := hCon.1.1.1.2 p hProfile.2.2.2.1
  exact ⟨mapped,fa,fb,fd,fp,hMap,ha,hb,hd,hp,map_profile hm hmN hCon hPres hGates hProfile hMap hMapped ha hb hd hp⟩

/-- Connect the accepted initial profile to the uniform source ProbeProfile.
The image node graph and old d are constructed with existing interfaces. -/
theorem initial_profile (hM : FirstOrder.Theory.Models M nativeZF)
    {w D S zero mul A b W E e I G O node gen a d ad oa ob oad : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ v, ¬ (Project.FirstOrderSemantics.reduct M).mem v zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hm : LeftCancelMonoid D mul e) (hAlpha : Alphabet D mul e S I A E)
    (hW : WordCarrier w D S mul A b W) (hb : (Project.FirstOrderSemantics.reduct M).mem b D)
    (hG : MultiplicationGraph hM w D S zero mul A b W E G)
    (hO : OldGraph zero D O) (hOmap : MapsTo D W O) (hn : MapsTo w D node)
    (hgen : (Project.FirstOrderSemantics.reduct M).mem gen W)
    (ha : Old zero D a oa) (hOldb : Old zero D b ob) (hOldad : Old zero D ad oad)
    (hd : (Project.FirstOrderSemantics.reduct M).mem d D) (had : Product mul a d ad)
    (hProfile : ConstructionProbeProfiles.ProfileLaws w D zero W G node gen oa ob oad) :
    ∃ mapped od, NodeMap node O mapped ∧ Old zero D d od ∧ ProbeProfile w W G oa ob od gen mapped := by
  obtain ⟨mapped,hMapped,hMap⟩ := exists_node_map hM hn hOmap
  obtain ⟨od,hOldd⟩ := exists_old hM (zero := zero) hd
  refine ⟨mapped,od,hMap,hOldd,old_word hM hz hzw hW ha,old_word hM hz hzw hW hOldb,
    old_word hM hz hzw hW hOldd,hgen,hMapped,oad,old_word hM hz hzw hW hOldad,
    ConstructionProbeOldEmbedding.old_mul hM hw hz hzw hm hAlpha hW hb hG ha hOldd hOldad had,hProfile.1,hProfile.2.1,?_,hProfile.2.2.2⟩
  intro x hx
  apply (and_comm.trans (hProfile.2.2.1 x hx)).trans
  constructor
  · rintro ⟨i,n,on,hi,hin,hon,hxon⟩
    exact ⟨i,on,hi,(hMap i on).mpr ⟨n,hin,(hO n on).mpr hon⟩,hxon⟩
  · rintro ⟨i,on,hi,hin,hxon⟩
    obtain ⟨n,hin,hon⟩ := (hMap i on).mp hin
    exact ⟨i,n,on,hi,hin,(hO n on).mp hon,hxon⟩

/-- Construct one fixed extension, its old gates, and preservation of every old
profile. The extension parameters are independent of all profile parameters. -/
theorem exists_probe_successor (hM : FirstOrder.Theory.Models M nativeZF)
    {w D S zero mul A b E e I pathNode F projection : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ v, ¬ (Project.FirstOrderSemantics.reduct M).mem v zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hm : LeftCancelMonoid D mul e) (hc : Conical D mul e) (hAlpha : Alphabet D mul e S I A E)
    (hb : (Project.FirstOrderSemantics.reduct M).mem b D) (hbne : b ≠ e)
    (hCone : ConstructionProbeCones.ConeLaws w D mul e zero pathNode F S projection A)
    (hJ : ConditionalJoins D mul) :
    ∃ W unit J G O,
      WordCarrier w D S mul A b W ∧ Old zero D e unit ∧
      ConstructionProbeLetters.Representatives W W J ∧ MapsTo J W G ∧
      MultiplicationGraph hM w D S zero mul A b W E G ∧
      LeftCancelMonoid W G unit ∧ Conical W G unit ∧ ConditionalJoins W G ∧
      OldGraph zero D O ∧ Conservative D W mul G O ∧ HasOldGates D W mul G O ∧
      ∀ a0 b0 d0 p0 node0, ProbeProfile w D mul a0 b0 d0 p0 node0 →
        ∃ mapped fa fb fd fp, NodeMap node0 O mapped ∧ PureKuratowski.PairMember M a0 fa O ∧
          PureKuratowski.PairMember M b0 fb O ∧ PureKuratowski.PairMember M d0 fd O ∧
          PureKuratowski.PairMember M p0 fp O ∧ ProbeProfile w W G fa fb fd fp mapped := by
  obtain ⟨W,unit,J,G,hW,hUnit,hWW,hGmap,hG,hmW,hcW,hJW⟩ :=
    ConstructionProbeConditionalJoins.exists_extension hM hw hz hzw hm hc hAlpha hb hbne hCone hJ
  obtain ⟨O,hO,hEmb,hCon⟩ := ConstructionProbeConservative.exists_conservative_old hM hw hz hzw hm hAlpha hW hb hG hUnit hCone
  have hGates := probe_has_old_gates hM hw hz hzw hm hAlpha hW hb hG hUnit hO hJ hCon
  have hPres : PreservesProducts mul G O := fun x y z fx fy fz hp hx hy hzv => hEmb.2.1 x y z fx fy fz hx hy hzv hp
  refine ⟨W,unit,J,G,O,hW,hUnit,hWW,hGmap,hG,hmW,hcW,hJW,hO,hCon,hGates,?_⟩
  intro a0 b0 d0 p0 node0 hProfile
  exact exists_mapped_profile hM hm hmW hCon hPres hGates hProfile

def oldGate {m : Nat} (D N mul mulN f q g fg : Fin m) : Project.Formula 1 m :=
  (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge f g fg)) (.conj (ProjectSyntax.encode id
    (ConstructionBaseMonoid.divides N mulN q fg)) (.conj (.forallE (.forallE (.imp (ProjectSyntax.encode id
    (Source.SetLanguage.edge f.succ.succ 1 0)) (.iff (ProjectSyntax.encode id
    (ConstructionBaseMonoid.divides N.succ.succ mulN.succ.succ q.succ.succ 0)) (ProjectSyntax.encode id
    (ConstructionBaseMonoid.divides D.succ.succ mul.succ.succ g.succ.succ 1)))))) (.forallE (.forallE (.imp
    (ProjectSyntax.encode id (Source.SetLanguage.edge f.succ.succ 1 0)) (.imp (.neg (ProjectSyntax.encode id
    (ConstructionBaseMonoid.divides N.succ.succ mulN.succ.succ 0 q.succ.succ))) (.forallE (.imp (.mem
    (.bound 0) (.bound N.succ.succ.succ)) (.iff (.conj (ProjectSyntax.encode id
    (ConstructionBaseMonoid.divides N.succ.succ.succ mulN.succ.succ.succ q.succ.succ.succ 0))
    (ProjectSyntax.encode id (ConstructionBaseMonoid.divides N.succ.succ.succ mulN.succ.succ.succ 1 0)))
    (.conj (ProjectSyntax.encode id (ConstructionBaseMonoid.divides N.succ.succ.succ mulN.succ.succ.succ
    fg.succ.succ.succ 0)) (ProjectSyntax.encode id (ConstructionBaseMonoid.divides N.succ.succ.succ
    mulN.succ.succ.succ 1 0)))))))))))))

theorem oldGate_freeClosed {m : Nat} (D N mul mulN f q g fg : Fin m) : (oldGate D N mul mulN f q g fg).FreeClosed := by
  simp -implicitDefEqProofs [oldGate,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed]

theorem oldGate_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (D N mul mulN f q g fg : Fin m) :
    Project.Formula.satisfies env (oldGate D N mul mulN f q g fg) ↔
      OldGate (env.bound D) (env.bound N) (env.bound mul) (env.bound mulN) (env.bound f) (env.bound q) (env.bound g) (env.bound fg) := by
  simp only [oldGate,OldGate,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_neg_iff,Project.Formula.satisfies_iff_iff,Project.Formula.satisfies_mem_iff,
    Project.Term.eval_bound,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    KuratowskiZF.source_edge,ConstructionBaseMonoid.divides_semantics (M := M)]
  rfl

def hasOldGates {m : Nat} (D N mul mulN f : Fin m) : Project.Formula 1 m :=
  (.forallE (.imp (.mem (.bound 0) (.bound N.succ)) (.imp (.existsE (.existsE (.conj (ProjectSyntax.encode
    id (Source.SetLanguage.edge f.succ.succ.succ 1 0)) (ProjectSyntax.encode id
    (ConstructionBaseMonoid.divides N.succ.succ.succ mulN.succ.succ.succ 2 0))))) (.disj (.existsE
    (ProjectSyntax.encode id (Source.SetLanguage.edge f.succ.succ 0 1))) (.existsE (.existsE (oldGate
    D.succ.succ.succ N.succ.succ.succ mul.succ.succ.succ mulN.succ.succ.succ f.succ.succ.succ 2 1 0)))))))

theorem hasOldGates_freeClosed {m : Nat} (D N mul mulN f : Fin m) : (hasOldGates D N mul mulN f).FreeClosed := by
  simp -implicitDefEqProofs [hasOldGates,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed ,oldGate_freeClosed]

theorem hasOldGates_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (D N mul mulN f : Fin m) :
    Project.Formula.satisfies env (hasOldGates D N mul mulN f) ↔
      HasOldGates (env.bound D) (env.bound N) (env.bound mul) (env.bound mulN) (env.bound f) := by
  simp only [hasOldGates,HasOldGates,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_disj_iff,
    Project.Formula.satisfies_mem_iff,
    Project.Term.eval_bound,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    KuratowskiZF.source_edge,ConstructionBaseMonoid.divides_semantics (M := M),
    oldGate_semantics hM]
  rfl

def probeProfile {m : Nat} (w D mul a b d p node : Fin m) : Project.Formula 1 m :=
  (.conj (.mem (.bound a) (.bound D)) (.conj (.mem (.bound b) (.bound D)) (.conj (.mem (.bound d) (.bound
    D)) (.conj (.mem (.bound p) (.bound D)) (.conj (ProjectSyntax.encode id (Source.SetLanguage.mapsTo node
    w D)) (.existsE (.conj (.mem (.bound 0) (.bound D.succ)) (.conj (ProjectSyntax.encode id
    (ForcingDiagramOrder.product mul.succ a.succ d.succ 0)) (.conj (ProjectSyntax.encode id
    (ForcingDiagramOrder.product mul.succ p.succ b.succ 0)) (.conj (.neg (ProjectSyntax.encode id
    (ConstructionBaseMonoid.divides D.succ mul.succ p.succ a.succ))) (.conj (.forallE (.imp (.mem (.bound 0)
    (.bound D.succ.succ)) (.iff (.conj (ProjectSyntax.encode id (ConstructionBaseMonoid.divides D.succ.succ
    mul.succ.succ 0 a.succ.succ)) (ProjectSyntax.encode id (ConstructionBaseMonoid.divides D.succ.succ
    mul.succ.succ 0 p.succ.succ))) (ConstructionProbeCones.initialProfile w.succ.succ D.succ.succ
    mul.succ.succ node.succ.succ 0)))) (.forallE (.imp (.mem (.bound 0) (.bound D.succ.succ)) (.imp
    (ProjectSyntax.encode id (ConstructionBaseMonoid.divides D.succ.succ mul.succ.succ 0 a.succ.succ)) (.imp
    (.neg (ProjectSyntax.encode id (ConstructionBaseMonoid.divides D.succ.succ mul.succ.succ 0
    p.succ.succ))) (ConstructionProbeCones.joinProperty D.succ.succ mul.succ.succ 0 p.succ.succ
    1))))))))))))))))

theorem probeProfile_freeClosed {m : Nat} (w D mul a b d p node : Fin m) : (probeProfile w D mul a b d p node).FreeClosed := by
  simp -implicitDefEqProofs [probeProfile,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed ,ConstructionProbeCones.initialProfile_freeClosed,ConstructionProbeCones.joinProperty_freeClosed]

theorem probeProfile_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w D mul a b d p node : Fin m) :
    Project.Formula.satisfies env (probeProfile w D mul a b d p node) ↔
      ProbeProfile (env.bound w) (env.bound D) (env.bound mul) (env.bound a) (env.bound b) (env.bound d) (env.bound p) (env.bound node) := by
  simp only [probeProfile,ProbeProfile,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_neg_iff,Project.Formula.satisfies_iff_iff,Project.Formula.satisfies_mem_iff,
    Project.Term.eval_bound,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ConstructionBaseMonoid.divides_semantics (M := M),
    ForcingDiagramOrder.product_semantics (M := M),ForcingSupportSize.mapsTo_semantics (M := M) ,ConstructionProbeCones.initialProfile_semantics hM,ConstructionProbeCones.joinProperty_semantics hM]
  rfl

def mapSentence : Project.Sentence where
  formula := Project.Formula.forallClosure 13
    (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid (1 : Fin 13) (3 : Fin 13) (5 : Fin
    13))) (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid (2 : Fin 13) (4 : Fin 13) (6
    : Fin 13))) (.imp (ConstructionProbeConservativeSyntax.conservative (1 : Fin 13) (2 : Fin 13) (3 : Fin
    13) (4 : Fin 13) (7 : Fin 13)) (.imp (ConstructionProbeLiftHomSyntax.preservesProducts (3 : Fin 13) (4 :
    Fin 13) (7 : Fin 13)) (.imp (hasOldGates (1 : Fin 13) (2 : Fin 13) (3 : Fin 13) (4 : Fin 13) (7 : Fin
    13)) (.imp (probeProfile (0 : Fin 13) (1 : Fin 13) (3 : Fin 13) (8 : Fin 13) (9 : Fin 13) (10 : Fin 13)
    (11 : Fin 13) (12 : Fin 13)) (.existsE (.existsE (.existsE (.existsE (.existsE (.conj
    (ConstructionProbeMappedPathSyntax.nodeMap (17 : Fin 18) (12 : Fin 18) (4 : Fin 18)) (.conj
    (ProjectSyntax.encode id (Source.SetLanguage.edge (12 : Fin 18) (13 : Fin 18) (3 : Fin 18))) (.conj
    (ProjectSyntax.encode id (Source.SetLanguage.edge (12 : Fin 18) (14 : Fin 18) (2 : Fin 18))) (.conj
    (ProjectSyntax.encode id (Source.SetLanguage.edge (12 : Fin 18) (15 : Fin 18) (1 : Fin 18))) (.conj
    (ProjectSyntax.encode id (Source.SetLanguage.edge (12 : Fin 18) (16 : Fin 18) (0 : Fin 18)))
    (probeProfile (5 : Fin 18) (7 : Fin 18) (9 : Fin 18) (3 : Fin 18) (2 : Fin 18) (1 : Fin 18) (0 : Fin 18)
    (4 : Fin 18))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
      ConstructionProbeConservativeSyntax.conservative_freeClosed,
      ConstructionProbeLiftHomSyntax.preservesProducts_freeClosed,
      hasOldGates_freeClosed,
      probeProfile_freeClosed,
      ConstructionProbeMappedPathSyntax.nodeMap_freeClosed]

theorem map_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence mapSentence).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) mapSentence]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_exists_iff,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),KuratowskiZF.source_edge,
    ConstructionProbeConservativeSyntax.conservative_semantics hM,
    ConstructionProbeLiftHomSyntax.preservesProducts_semantics hM,
    hasOldGates_semantics hM,
    probeProfile_semantics hM,
    ConstructionProbeMappedPathSyntax.nodeMap_semantics hM]
  exact fun hm hmN hCon hPres hGates hProfile => exists_mapped_profile hM hm hmN hCon hPres hGates hProfile

theorem map_kernel_certificate : FirstOrder.Derives nativeZF []
    (Project.fo_sentence mapSentence) := ModelTransfer.derives (fun _ hM => map_models hM)

def initialSentence : Project.Sentence where
  formula := Project.Formula.forallClosure 21
    (.imp (Project.Formula.isOmega (.bound (0 : Fin 21))) (.imp (Project.Formula.isEmpty (.bound (3 : Fin
    21))) (.imp (.mem (.bound (3 : Fin 21)) (.bound (0 : Fin 21))) (.imp (ProjectSyntax.encode id
    (ForcingDiagramPoset.leftCancelMonoid (1 : Fin 21) (4 : Fin 21) (9 : Fin 21))) (.imp
    (ConstructionProbeAlphabet.alphabet (1 : Fin 21) (4 : Fin 21) (9 : Fin 21) (2 : Fin 21) (10 : Fin 21) (5
    : Fin 21) (8 : Fin 21)) (.imp (ConstructionProbeWord.wordCarrier (0 : Fin 21) (1 : Fin 21) (2 : Fin 21)
    (4 : Fin 21) (5 : Fin 21) (6 : Fin 21) (7 : Fin 21)) (.imp (.mem (.bound (6 : Fin 21)) (.bound (1 : Fin
    21))) (.imp (ConstructionProbeWordMonoidSyntax.multiplicationGraph (0 : Fin 21) (1 : Fin 21) (2 : Fin
    21) (3 : Fin 21) (4 : Fin 21) (5 : Fin 21) (6 : Fin 21) (7 : Fin 21) (8 : Fin 21) (11 : Fin 21)) (.imp
    (ConstructionProbeOldEmbeddingSyntax.oldGraph (3 : Fin 21) (1 : Fin 21) (12 : Fin 21)) (.imp
    (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (12 : Fin 21) (1 : Fin 21) (7 : Fin 21))) (.imp
    (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (13 : Fin 21) (0 : Fin 21) (1 : Fin 21))) (.imp
    (.mem (.bound (14 : Fin 21)) (.bound (7 : Fin 21))) (.imp (old (3 : Fin 21) (1 : Fin 21) (15 : Fin 21)
    (18 : Fin 21)) (.imp (old (3 : Fin 21) (1 : Fin 21) (6 : Fin 21) (19 : Fin 21)) (.imp (old (3 : Fin 21)
    (1 : Fin 21) (17 : Fin 21) (20 : Fin 21)) (.imp (.mem (.bound (16 : Fin 21)) (.bound (1 : Fin 21)))
    (.imp (ProjectSyntax.encode id (ForcingDiagramOrder.product (4 : Fin 21) (15 : Fin 21) (16 : Fin 21) (17
    : Fin 21))) (.imp (ConstructionProbeProfiles.profileLaws (0 : Fin 21) (1 : Fin 21) (3 : Fin 21) (7 : Fin
    21) (11 : Fin 21) (13 : Fin 21) (14 : Fin 21) (18 : Fin 21) (19 : Fin 21) (20 : Fin 21)) (.existsE
    (.existsE (.conj (ConstructionProbeMappedPathSyntax.nodeMap (15 : Fin 23) (14 : Fin 23) (1 : Fin 23))
    (.conj (old (5 : Fin 23) (3 : Fin 23) (18 : Fin 23) (0 : Fin 23)) (probeProfile (2 : Fin 23) (9 : Fin
    23) (13 : Fin 23) (20 : Fin 23) (21 : Fin 23) (0 : Fin 23) (16 : Fin 23) (1 : Fin
    23))))))))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
      Project.Formula.isEmpty,ConstructionProbeAlphabet.alphabet_freeClosed,
      ConstructionProbeWord.wordCarrier_freeClosed,
      ConstructionProbeWordMonoidSyntax.multiplicationGraph_freeClosed,
      ConstructionProbeOldEmbeddingSyntax.oldGraph_freeClosed,
      old_freeClosed,
      ConstructionProbeProfiles.profileLaws_freeClosed,
      ConstructionProbeMappedPathSyntax.nodeMap_freeClosed,
      probeProfile_freeClosed]

theorem initial_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence initialSentence).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) initialSentence]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_isOmega_iff,Project.Formula.satisfies_isEmpty_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),ForcingSupportSize.mapsTo_semantics (M := M),ForcingDiagramOrder.product_semantics (M := M),ConstructionProbeAlphabet.alphabet_semantics hM,
    ConstructionProbeWord.wordCarrier_semantics hM,
    ConstructionProbeWordMonoidSyntax.multiplicationGraph_semantics hM,
    ConstructionProbeOldEmbeddingSyntax.oldGraph_semantics hM,
    old_semantics hM,
    ConstructionProbeProfiles.profileLaws_semantics hM,
    ConstructionProbeMappedPathSyntax.nodeMap_semantics hM,
    probeProfile_semantics hM]
  exact fun hw hz hzw hm hAlpha hW hb hG hO hOmap hn hgen ha hOldb hOldad hd had hProfile => initial_profile hM hw hz hzw hm hAlpha hW hb hG hO hOmap hn hgen ha hOldb hOldad hd had hProfile

theorem initial_kernel_certificate : FirstOrder.Derives nativeZF []
    (Project.fo_sentence initialSentence) := ModelTransfer.derives (fun _ hM => initial_models hM)

def successorSentence : Project.Sentence where
  formula := Project.Formula.forallClosure 13
    (.imp (Project.Formula.isOmega (.bound (0 : Fin 13))) (.imp (Project.Formula.isEmpty (.bound (3 : Fin
    13))) (.imp (.mem (.bound (3 : Fin 13)) (.bound (0 : Fin 13))) (.imp (ProjectSyntax.encode id
    (ForcingDiagramPoset.leftCancelMonoid (1 : Fin 13) (4 : Fin 13) (8 : Fin 13))) (.imp
    (ProjectSyntax.encode id (ForcingDiagramPoset.conical (1 : Fin 13) (4 : Fin 13) (8 : Fin 13))) (.imp
    (ConstructionProbeAlphabet.alphabet (1 : Fin 13) (4 : Fin 13) (8 : Fin 13) (2 : Fin 13) (9 : Fin 13) (5
    : Fin 13) (7 : Fin 13)) (.imp (.mem (.bound (6 : Fin 13)) (.bound (1 : Fin 13))) (.imp (.neg
    (Project.Formula.extensionalEq (.bound (6 : Fin 13)) (.bound (8 : Fin 13)))) (.imp
    (ConstructionProbeCones.coneLaws (0 : Fin 13) (1 : Fin 13) (4 : Fin 13) (8 : Fin 13) (3 : Fin 13) (10 :
    Fin 13) (11 : Fin 13) (2 : Fin 13) (12 : Fin 13) (5 : Fin 13)) (.imp
    (ConstructionProbeSharedIntersections.conditionalJoins (1 : Fin 13) (4 : Fin 13)) (.existsE (.existsE
    (.existsE (.existsE (.existsE (.conj (ConstructionProbeWord.wordCarrier (5 : Fin 18) (6 : Fin 18) (7 :
    Fin 18) (9 : Fin 18) (10 : Fin 18) (11 : Fin 18) (4 : Fin 18)) (.conj (old (8 : Fin 18) (6 : Fin 18) (13
    : Fin 18) (3 : Fin 18)) (.conj (ConstructionProbeLetters.representatives (4 : Fin 18) (4 : Fin 18) (2 :
    Fin 18)) (.conj (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (1 : Fin 18) (2 : Fin 18) (4 : Fin
    18))) (.conj (ConstructionProbeWordMonoidSyntax.multiplicationGraph (5 : Fin 18) (6 : Fin 18) (7 : Fin
    18) (8 : Fin 18) (9 : Fin 18) (10 : Fin 18) (11 : Fin 18) (4 : Fin 18) (12 : Fin 18) (1 : Fin 18))
    (.conj (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid (4 : Fin 18) (1 : Fin 18) (3 : Fin
    18))) (.conj (ProjectSyntax.encode id (ForcingDiagramPoset.conical (4 : Fin 18) (1 : Fin 18) (3 : Fin
    18))) (.conj (ConstructionProbeSharedIntersections.conditionalJoins (4 : Fin 18) (1 : Fin 18)) (.conj
    (ConstructionProbeOldEmbeddingSyntax.oldGraph (8 : Fin 18) (6 : Fin 18) (0 : Fin 18)) (.conj
    (ConstructionProbeConservativeSyntax.conservative (6 : Fin 18) (4 : Fin 18) (9 : Fin 18) (1 : Fin 18) (0
    : Fin 18)) (.conj (hasOldGates (6 : Fin 18) (4 : Fin 18) (9 : Fin 18) (1 : Fin 18) (0 : Fin 18))
    (.forallE (.forallE (.forallE (.forallE (.forallE (.imp (probeProfile (10 : Fin 23) (11 : Fin 23) (14 :
    Fin 23) (4 : Fin 23) (3 : Fin 23) (2 : Fin 23) (1 : Fin 23) (0 : Fin 23)) (.existsE (.existsE (.existsE
    (.existsE (.existsE (.conj (ConstructionProbeMappedPathSyntax.nodeMap (5 : Fin 28) (10 : Fin 28) (4 :
    Fin 28)) (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge (10 : Fin 28) (9 : Fin 28) (3 : Fin
    28))) (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge (10 : Fin 28) (8 : Fin 28) (2 : Fin 28)))
    (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge (10 : Fin 28) (7 : Fin 28) (1 : Fin 28)))
    (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge (10 : Fin 28) (6 : Fin 28) (0 : Fin 28)))
    (probeProfile (15 : Fin 28) (14 : Fin 28) (11 : Fin 28) (3 : Fin 28) (2 : Fin 28) (1 : Fin 28) (0 : Fin
    28) (4 : Fin 28))))))))))))))))))))))))))))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
      Project.Formula.isEmpty,Project.Formula.extensionalEq,
      ConstructionProbeAlphabet.alphabet_freeClosed,
      ConstructionProbeCones.coneLaws_freeClosed,
      ConstructionProbeSharedIntersections.conditionalJoins_freeClosed,
      probeProfile_freeClosed,
      ConstructionProbeWord.wordCarrier_freeClosed,
      old_freeClosed,
      ConstructionProbeLetters.representatives_freeClosed,
      ConstructionProbeWordMonoidSyntax.multiplicationGraph_freeClosed,
      ConstructionProbeOldEmbeddingSyntax.oldGraph_freeClosed,
      ConstructionProbeConservativeSyntax.conservative_freeClosed,
      hasOldGates_freeClosed,
      ConstructionProbeMappedPathSyntax.nodeMap_freeClosed]

theorem successor_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence successorSentence).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) successorSentence]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_neg_iff,
    Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_isOmega_iff,Project.Formula.satisfies_isEmpty_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM),
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),ForcingDiagramPoset.conical_semantics (M := M),
    ForcingSupportSize.mapsTo_semantics (M := M),KuratowskiZF.source_edge,
    ConstructionProbeAlphabet.alphabet_semantics hM,
    ConstructionProbeCones.coneLaws_semantics hM,
    ConstructionProbeSharedIntersections.conditionalJoins_semantics hM,
    probeProfile_semantics hM,
    ConstructionProbeWord.wordCarrier_semantics hM,
    old_semantics hM,
    ConstructionProbeLetters.representatives_semantics hM,
    ConstructionProbeWordMonoidSyntax.multiplicationGraph_semantics hM,
    ConstructionProbeOldEmbeddingSyntax.oldGraph_semantics hM,
    ConstructionProbeConservativeSyntax.conservative_semantics hM,
    hasOldGates_semantics hM,
    ConstructionProbeMappedPathSyntax.nodeMap_semantics hM]
  exact fun hw hz hzw hm hc hAlpha hb hbne hCone hJ => exists_probe_successor hM hw hz hzw hm hc hAlpha hb hbne hCone hJ

theorem successor_kernel_certificate : FirstOrder.Derives nativeZF []
    (Project.fo_sentence successorSentence) := ModelTransfer.derives (fun _ hM => successor_models hM)

end PPAC.Migration.ConstructionPersistentProfiles
