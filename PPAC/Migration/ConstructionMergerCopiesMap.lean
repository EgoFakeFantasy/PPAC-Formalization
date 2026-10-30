/- Pinned Algebra/ConservativeExtensions copiesMap/injective/act/factors/
common_below. Consumer: Word.transport_conservative / mergerSimulation_conservative.
Reuse the existing exact Value/Graph formulas and native graph constructor. -/
import PPAC.Migration.ConstructionMergerPushout

namespace PPAC.Migration.ConstructionMergerCopiesMap
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionMergerPushout (Presentation)
open ConstructionMergerCopies (copy_eq_iff representative copy_injective)
open ConstructionMergerRelations (product_range)
open ConstructionMergerPrescriptionMap (Mapped rel_map rel_map_iff starts_of_rel_map)
open ConstructionProbeLettersMap (Value Graph value value_freeClosed value_semantics)
open ConstructionProbeAction (projected projected_indices projected_range)
open ConstructionProbeConservative (Conservative)
open ConstructionProbeSharedIntersections (ConditionalJoins)
open ConstructionProbeLiftHom (PreservesProducts)
open ConstructionMergerCopyCones (Reaches reaches_copy_iff reaches_same_copy_iff)
open ConstructionBaseMonoid (Divides)
open ForcingSupportSize (MapsTo Injection)
open ForcingDiagramOrder (Product)
open ForcingDiagramPoset (LeftCancelMonoid)
open ForcingConditionGraphs (function_input function_unique)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

/-- Source Conservative.common_below, using the existing four fields and
conditional join producer, without a new order or hull construction. -/
theorem base_common_below {D N mul mulN e f x y fx fy z : M.Carrier .set}
    (hm : LeftCancelMonoid D mul e) (hf : Conservative D N mul mulN f) (hJ : ConditionalJoins D mul)
    (hfx : PureKuratowski.PairMember M x fx f) (hfy : PureKuratowski.PairMember M y fy f)
    (hz : (Project.FirstOrderSemantics.reduct M).mem z N)
    (hxz : Divides N mulN fx z) (hyz : Divides N mulN fy z) :
    ∃ j fj, (Project.FirstOrderSemantics.reduct M).mem j D ∧ PureKuratowski.PairMember M j fj f ∧
      Divides D mul x j ∧ Divides D mul y j ∧ Divides N mulN fj z := by
  obtain ⟨a,ha,hxa,hya⟩ := hf.2.2.2 x y fx fy hfx hfy ⟨z,hz,hxz,hyz⟩
  obtain ⟨j,hj,hJoin⟩ := hJ x y a (function_input hf.1.1.1 hfx) (function_input hf.1.1.1 hfy) ha hxa hya
  have hSelf : Divides D mul j j := ⟨e,hm.1.1,((hm.1.2 j hj j).2).mpr rfl⟩
  obtain ⟨fj,hfj,_⟩ := hf.1.1.1.2 j hj
  exact ⟨j,fj,hj,hfj,((hJoin j hj).mpr hSelf).1,((hJoin j hj).mpr hSelf).2,
    ((hf.2.2.1 x y j fx fy fj hfx hfy hfj hJoin) z hz).mp ⟨hxz,hyz⟩⟩

/-- Source Conservative.cone_residual: the SAME old residual works in the
old monoid and against every new target factor, by preserved intersections. -/
theorem base_residual {D N mul mulN e eN f x a fx fa t z : M.Carrier .set}
    (hm : LeftCancelMonoid D mul e) (hmN : LeftCancelMonoid N mulN eN)
    (hf : Conservative D N mul mulN f) (hPres : PreservesProducts mul mulN f) (hJ : ConditionalJoins D mul)
    (hfx : PureKuratowski.PairMember M x fx f) (hfa : PureKuratowski.PairMember M a fa f)
    (ht : (Project.FirstOrderSemantics.reduct M).mem t N) (hat : Product mulN fa t z)
    (hxz : Divides N mulN fx z) :
    ∃ r fr, (Project.FirstOrderSemantics.reduct M).mem r D ∧ PureKuratowski.PairMember M r fr f ∧
      (∀ u au, (Project.FirstOrderSemantics.reduct M).mem u D → Product mul a u au →
        (Divides D mul x au ↔ Divides D mul r u)) ∧
      ∀ u au, (Project.FirstOrderSemantics.reduct M).mem u N → Product mulN fa u au →
        (Divides N mulN fx au ↔ Divides N mulN fr u) := by
  have hx := function_input hf.1.1.1 hfx
  have ha := function_input hf.1.1.1 hfa
  have hfaN := hf.1.1.2 a fa hfa
  obtain ⟨b,hb,hxb,hab⟩ := hf.2.2.2 x a fx fa hfx hfa ⟨z,product_range hmN hfaN ht hat,hxz,t,ht,hat⟩
  obtain ⟨j,hj,hJoin⟩ := hJ x a b hx ha hb hxb hab
  have hSelf : Divides D mul j j := ⟨e,hm.1.1,((hm.1.2 j hj j).2).mpr rfl⟩
  obtain ⟨r,hr,har⟩ := ((hJoin j hj).mpr hSelf).2
  obtain ⟨fr,hfr,_⟩ := hf.1.1.1.2 r hr
  obtain ⟨fj,hfj,_⟩ := hf.1.1.1.2 j hj
  have hPresJoin := hf.2.2.1 x a j fx fa fj hfx hfa hfj hJoin
  have hafr := hPres a r j fa fr fj har hfa hfr hfj
  refine ⟨r,fr,hr,hfr,?_,?_⟩
  · intro u au hu hau
    have hCancel := ConstructionProbeConditionalJoins.left_mul_dvd_iff hm ha hr hu har hau
    exact ⟨fun h => hCancel.mp ((hJoin au (product_range hm ha hu hau)).mp ⟨h,u,hu,hau⟩),
      fun h => ((hJoin au (product_range hm ha hu hau)).mpr (hCancel.mpr h)).1⟩
  · intro u au hu hau
    have hCancel := ConstructionProbeConditionalJoins.left_mul_dvd_iff hmN hfaN (hf.1.1.2 r fr hfr) hu hafr hau
    exact ⟨fun h => hCancel.mp ((hPresJoin au (product_range hmN hfaN hu hau)).mp ⟨h,u,hu,hau⟩),
      fun h => ((hPresJoin au (product_range hmN hfaN hu hau)).mpr (hCancel.mpr h)).1⟩

section Copies
variable {w n zero D mul e P C L projection A W T B G unit O roots : M.Carrier .set}
variable {N mulN eN PN CN LN projectionN AN WN TN BN GN unitN ON rootsN f g : M.Carrier .set}
variable (hA : Presentation w n zero D mul e P C L projection A W T B G unit O roots)
variable (hB : Presentation w n zero N mulN eN PN CN LN projectionN AN WN TN BN GN unitN ON rootsN)
include hA hB

theorem value_unique (hf : MapsTo D N f) (hPres : PreservesProducts mul mulN f) (hMap : Mapped P f PN)
    {c d d' : M.Carrier .set} (hd : Value projection projectionN f c d) (hd' : Value projection projectionN f c d') : d = d' := by
  obtain ⟨i,x,fx,hxc,hfx,hfd⟩ := hd
  obtain ⟨j,y,fy,hyc,hfy,hfd'⟩ := hd'
  exact (copy_eq_iff hB.equality hfd hfd').mpr
    (rel_map hA.prescription hf hPres hMap ((copy_eq_iff hA.equality hxc hyc).mp rfl) hfx hfy)

theorem exists_graph (hM : FirstOrder.Theory.Models M nativeZF)
    (hf : MapsTo D N f) (hPres : PreservesProducts mul mulN f) (hMap : Mapped P f PN) :
    ∃ g, MapsTo L LN g ∧ Graph L projection projectionN f g := by
  let schema : Project.BinarySchema 3 := { body := value 2 3 4 1 0,freeClosed := value_freeClosed .. }
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 3 := {
    bound := Fin.cases projection (Fin.cases projectionN (fun _ => f)),free := fun _ => L }
  have he c d : schema.denote env c d ↔ Value projection projectionN f c d :=
    value_semantics hM (env.push c |>.push d) 2 3 4 1 0
  obtain ⟨g,hg,hGraph⟩ := ZF.exists_setFunctionFromTo_of_denote (ModelTransfer.project_models_iff.mp hM)
    (KuratowskiZF.interpretation hM) schema env (source := L) (target := LN) (by
      intro c hc
      obtain ⟨i,x,hi,hx,hic⟩ := representative hA.representatives hA.copies hA.projection_law hc
      obtain ⟨fx,hfx,_⟩ := hf.1.2 x hx
      obtain ⟨d,_,hid⟩ := projected hM hB.representatives hB.projection_map hi (hf.2 x fx hfx)
      exact ⟨d,(he c d).mpr ⟨i,x,fx,hic,hfx,hid⟩⟩) (by
      intro c _ d d' hd hd'
      exact value_unique hA hB hf hPres hMap ((he c d).mp hd) ((he c d').mp hd')) (by
      intro c d _ hd
      obtain ⟨_,_,_,_,_,hid⟩ := (he c d).mp hd
      exact projected_range hB.projection_map hid)
  exact ⟨g,(ForcingSupportSize.native_mapsTo hM L LN g).mpr hg,
    fun c d => (hGraph c d).trans (and_congr_right fun _ => he c d)⟩

theorem map_copy (hM : FirstOrder.Theory.Models M nativeZF)
    (hf : MapsTo D N f) (hPres : PreservesProducts mul mulN f) (hMap : Mapped P f PN)
    (hg : Graph L projection projectionN f g) {i x fx c d : M.Carrier .set}
    (hic : Product projection i x c) (hfx : PureKuratowski.PairMember M x fx f) :
    PureKuratowski.PairMember M c d g ↔ Product projectionN i fx d := by
  constructor
  · intro hcd
    obtain ⟨d',_,hid'⟩ := projected hM hB.representatives hB.projection_map
      (projected_indices hA.representatives hA.projection_map hic).1 (hf.2 x fx hfx)
    have he := value_unique hA hB hf hPres hMap ((hg c d).mp hcd).2 ⟨i,x,fx,hic,hfx,hid'⟩
    exact he.symm ▸ hid'
  · intro hid
    exact (hg c d).mpr ⟨projected_range hA.projection_map hic,i,x,fx,hic,hfx,hid⟩

theorem graph_injective (hf : Conservative D N mul mulN f) (hPres : PreservesProducts mul mulN f)
    (hMap : Mapped P f PN) (hgm : MapsTo L LN g) (hg : Graph L projection projectionN f g) : Injection L LN g := by
  refine ⟨hgm,?_⟩
  intro c d v hc hd
  obtain ⟨i,x,fx,hic,hfx,hiv⟩ := ((hg c v).mp hc).2
  obtain ⟨j,y,fy,hjd,hfy,hjv⟩ := ((hg d v).mp hd).2
  exact (copy_eq_iff hA.equality hic hjd).mpr
    ((rel_map_iff hA.monoid hB.monoid hA.prescription hf hPres hMap hfx hfy).mp ((copy_eq_iff hB.equality hiv hjv).mp rfl))

theorem map_act (hM : FirstOrder.Theory.Models M nativeZF)
    (hf : MapsTo D N f) (hPres : PreservesProducts mul mulN f) (hMap : Mapped P f PN)
    (hg : Graph L projection projectionN f g) : ConstructionMergerEvaluation.Equivariant A f g AN := by
  intro c x d gc fx gd hAct hc hx hd
  obtain ⟨_,i,a,ax,ha,hic,hax,hid⟩ := (hA.copy_action c x d).mp hAct
  obtain ⟨fa,hfa,_⟩ := hf.1.2 a ha
  obtain ⟨fax,hfax,_⟩ := hf.1.2 ax (projected_indices hA.representatives hA.projection_map hid).2
  have hicN := (map_copy hA hB hM hf hPres hMap hg hic hfa).mp hc
  have hidN := (map_copy hA hB hM hf hPres hMap hg hid hfax).mp hd
  exact (hB.copy_law i fa fax gc fx gd (hf.2 x fx hx) hicN (hPres a x ax fa fx fax hax hfa hx hfax)).mpr hidN


/-- Source copiesMap_factors: every right factor between mapped copies lies
in the old base, including the different-index prescription-overlap case. -/
theorem copy_factors (hf : Conservative D N mul mulN f) (hPres : PreservesProducts mul mulN f)
    (hMap : Mapped P f PN) (hg : Graph L projection projectionN f g)
    {c d gc gd m : M.Carrier .set}
    (hc : PureKuratowski.PairMember M c gc g) (hd : PureKuratowski.PairMember M d gd g)
    (hAct : Product AN gc m gd) : ∃ a, PureKuratowski.PairMember M a m f := by
  obtain ⟨i,x,fx,hic,hfx,hicN⟩ := ((hg c gc).mp hc).2
  obtain ⟨j,y,fy,hjd,hfy,hjdN⟩ := ((hg d gd).mp hd).2
  have hmN := ((hB.copy_action gc m gd).mp hAct).1
  obtain ⟨fxm,_,hfxm⟩ := (hB.monoid.2.1 fx (hf.1.1.2 x fx hfx)).1 m hmN
  have hifxm := (hB.copy_law i fx fxm gc m gd hmN hicN hfxm).mp hAct
  by_cases hij : i = j
  · subst j
    have he := copy_injective hB.representatives hB.projection_map hB.equality hifxm hjdN
    exact hf.2.1 x y m fx fy hfx hfy hmN (he ▸ hfxm)
  · have hr := (copy_eq_iff hB.equality hifxm hjdN).mp rfl
    obtain ⟨a,b,fa,fb,t,_,hfa,hfb,ht,hat,hbt⟩ := starts_of_rel_map hMap hij hr
    obtain ⟨s,hs⟩ := hf.2.1 b y t fb fy hfb hfy ht hbt
    have ha := function_input hf.1.1.1 hfa
    have hsD := function_input hf.1.1.1 hs
    obtain ⟨aS,haS,has⟩ := (hA.monoid.2.1 a ha).1 s hsD
    obtain ⟨faS,hfaS,_⟩ := hf.1.1.1.2 aS haS
    have he := (hB.monoid.2.1 fa (hf.1.1.2 a fa hfa)).2.1 t fxm faS ht
      hat (hPres a s aS fa t faS has hfa hs hfaS)
    exact hf.2.1 x aS m fx faS hfx hfaS hmN (he ▸ hfxm)


/-- Source copiesMap_common_below, against every target copy, with the
same old residuals supplied by the base conservative morphism. -/
theorem copy_common_below (hM : FirstOrder.Theory.Models M nativeZF)
    (hf : Conservative D N mul mulN f) (hPres : PreservesProducts mul mulN f)
    (hMap : Mapped P f PN) (hJoins : ConditionalJoins D mul)
    (hg : Graph L projection projectionN f g)
    {c d gc gd z : M.Carrier .set}
    (hc : PureKuratowski.PairMember M c gc g) (hd : PureKuratowski.PairMember M d gd g)
    (hcz : Reaches N AN gc z) (hdz : Reaches N AN gd z) :
    ∃ k gk, (Project.FirstOrderSemantics.reduct M).mem k L ∧ PureKuratowski.PairMember M k gk g ∧
      Reaches D A c k ∧ Reaches D A d k ∧ Reaches N AN gk z := by
  obtain ⟨i,x,fx,hic,hfx,hicN⟩ := ((hg c gc).mp hc).2
  obtain ⟨j,y,fy,hjd,hfy,hjdN⟩ := ((hg d gd).mp hd).2
  obtain ⟨u,fxu,hu,hfxu,hiz⟩ := (reaches_copy_iff hB.monoid hB.representatives hB.projection_map hB.copy_law hicN).mp hcz
  obtain ⟨v,fyv,hv,hfyv,hjz⟩ := (reaches_copy_iff hB.monoid hB.representatives hB.projection_map hB.copy_law hjdN).mp hdz
  have hi := (projected_indices hA.representatives hA.projection_map hic).1
  by_cases hij : i = j
  · subst j
    have he := copy_injective hB.representatives hB.projection_map hB.equality hiz hjz
    obtain ⟨k,fk,hk,hfk,hxk,hyk,hfkz⟩ := base_common_below hA.monoid hf hJoins hfx hfy
      (product_range hB.monoid (hf.1.1.2 x fx hfx) hu hfxu) ⟨u,hu,hfxu⟩ ⟨v,hv,he.symm ▸ hfyv⟩
    obtain ⟨ck,hck,hik⟩ := projected hM hA.representatives hA.projection_map hi hk
    obtain ⟨gk,_,hikN⟩ := projected hM hB.representatives hB.projection_map hi (hf.1.1.2 k fk hfk)
    refine ⟨ck,gk,hck,(map_copy hA hB hM hf.1.1 hPres hMap hg hik hfk).mpr hikN,?_,?_,?_⟩
    · exact (reaches_same_copy_iff hA.monoid hA.representatives hA.projection_map hA.equality hA.copy_law hic hik).mpr hxk
    · exact (reaches_same_copy_iff hA.monoid hA.representatives hA.projection_map hA.equality hA.copy_law hjd hik).mpr hyk
    · obtain ⟨t,ht,hft⟩ := hfkz
      exact (reaches_copy_iff hB.monoid hB.representatives hB.projection_map hB.copy_law hikN).mpr ⟨t,fxu,ht,hft,hiz⟩
  · obtain ⟨a,b,fa,fb,t,hStart,hfa,hfb,ht,hat,hbt⟩ := starts_of_rel_map hMap hij ((copy_eq_iff hB.equality hiz hjz).mp rfl)
    obtain ⟨r,fr,hr,hfr,hrOld,hrNew⟩ := base_residual hA.monoid hB.monoid hf hPres hJoins hfx hfa ht hat ⟨u,hu,hfxu⟩
    obtain ⟨s,fs,hs,hfs,hsOld,hsNew⟩ := base_residual hA.monoid hB.monoid hf hPres hJoins hfy hfb ht hbt ⟨v,hv,hfyv⟩
    obtain ⟨k,fk,hk,hfk,hrk,hsk,hfkt⟩ := base_common_below hA.monoid hf hJoins hfr hfs ht
      ((hrNew t fxu ht hat).mp ⟨u,hu,hfxu⟩) ((hsNew t fyv ht hbt).mp ⟨v,hv,hfyv⟩)
    have ha := function_input hf.1.1.1 hfa
    have hb := function_input hf.1.1.1 hfb
    obtain ⟨ak,hakD,hak⟩ := (hA.monoid.2.1 a ha).1 k hk
    obtain ⟨bk,hbkD,hbk⟩ := (hA.monoid.2.1 b hb).1 k hk
    have hRel := ConstructionMergerRelations.rel_mul hA.monoid hA.prescription hk
      (ConstructionMergerPrescriptionMap.rel_start hA.monoid hA.prescription hij hStart) hak hbk
    obtain ⟨ck,hck,hik⟩ := projected hM hA.representatives hA.projection_map hi hakD
    obtain ⟨dk,_,hjk⟩ := projected hM hA.representatives hA.projection_map
      (projected_indices hA.representatives hA.projection_map hjd).1 hbkD
    have hEq : ck = dk := (copy_eq_iff hA.equality hik hjk).mpr hRel
    have hjck : Product projection j bk ck := hEq.symm ▸ hjk
    obtain ⟨fak,hfak,_⟩ := hf.1.1.1.2 ak hakD
    obtain ⟨gk,_,hikN⟩ := projected hM hB.representatives hB.projection_map hi (hf.1.1.2 ak fak hfak)
    refine ⟨ck,gk,hck,(map_copy hA hB hM hf.1.1 hPres hMap hg hik hfak).mpr hikN,?_,?_,?_⟩
    · exact (reaches_same_copy_iff hA.monoid hA.representatives hA.projection_map hA.equality hA.copy_law hic hik).mpr ((hrOld k ak hk hak).mpr hrk)
    · exact (reaches_same_copy_iff hA.monoid hA.representatives hA.projection_map hA.equality hA.copy_law hjd hjck).mpr ((hsOld k bk hk hbk).mpr hsk)
    · obtain ⟨q,hq,hfkq⟩ := hfkt
      have hafk := hPres a k ak fa fk fak hak hfa hfk hfak
      have hfaq := (hB.monoid.2.2 fa fk q fak t fxu (hf.1.1.2 a fa hfa) (hf.1.1.2 k fk hfk) hq hafk hfkq).mpr hat
      exact (reaches_copy_iff hB.monoid hB.representatives hB.projection_map hB.copy_law hikN).mpr ⟨q,fxu,hq,hfaq,hiz⟩

end Copies

/-- Arbitrary target right factors, not only those already known to be mapped. -/
def CopyFactors (AN f g : M.Carrier .set) : Prop := ∀ c d gc gd m,
  PureKuratowski.PairMember M c gc g → PureKuratowski.PairMember M d gd g →
    Product AN gc m gd → ∃ a, PureKuratowski.PairMember M a m f

/-- An old common lower copy below every target common upper copy. -/
def CopyCommon (D N L A AN g : M.Carrier .set) : Prop := ∀ c d gc gd z,
  PureKuratowski.PairMember M c gc g → PureKuratowski.PairMember M d gd g →
  Reaches N AN gc z → Reaches N AN gd z →
    ∃ k gk, (Project.FirstOrderSemantics.reduct M).mem k L ∧ PureKuratowski.PairMember M k gk g ∧
      Reaches D A c k ∧ Reaches D A d k ∧ Reaches N AN gk z

def Laws (D N L LN projection projectionN A AN f g : M.Carrier .set) : Prop :=
  Injection L LN g ∧ Graph L projection projectionN f g ∧
  ConstructionProbeLettersMapSyntax.RepresentativeLaw projection projectionN f g ∧
  ConstructionMergerEvaluation.Equivariant A f g AN ∧ CopyFactors AN f g ∧ CopyCommon D N L A AN g

theorem exists_system (hM : FirstOrder.Theory.Models M nativeZF)
    {w n zero D mul e P C L projection A W T B G unit O roots
     N mulN eN PN CN LN projectionN AN WN TN BN GN unitN ON rootsN f : M.Carrier .set}
    (hA : Presentation w n zero D mul e P C L projection A W T B G unit O roots)
    (hB : Presentation w n zero N mulN eN PN CN LN projectionN AN WN TN BN GN unitN ON rootsN)
    (hf : Conservative D N mul mulN f) (hPres : PreservesProducts mul mulN f)
    (hMap : Mapped P f PN) (hJoins : ConditionalJoins D mul) :
    ∃ g, Laws D N L LN projection projectionN A AN f g := by
  obtain ⟨g,hgm,hg⟩ := exists_graph hA hB hM hf.1.1 hPres hMap
  refine ⟨g,graph_injective hA hB hf hPres hMap hgm hg,hg,?_,
    map_act hA hB hM hf.1.1 hPres hMap hg,?_,?_⟩
  · intro i x fx c d hic hfx
    exact map_copy hA hB hM hf.1.1 hPres hMap hg hic hfx
  · intro c d gc gd m hc hd hAct
    exact copy_factors hA hB hf hPres hMap hg hc hd hAct
  · intro c d gc gd z hc hd hcz hdz
    exact copy_common_below hA hB hM hf hPres hMap hJoins hg hc hd hcz hdz

def copyFactors {m : Nat} (AN f g : Fin m) : Project.Formula 1 m :=
  (.forallE (.forallE (.forallE (.forallE (.forallE (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge
  g.succ.succ.succ.succ.succ 4 2)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge
  g.succ.succ.succ.succ.succ 3 1)) (.imp (ProjectSyntax.encode id (ForcingDiagramOrder.product
  AN.succ.succ.succ.succ.succ 2 0 1)) (.existsE (ProjectSyntax.encode id (Source.SetLanguage.edge
  f.succ.succ.succ.succ.succ.succ 0 1)))))))))))

theorem copyFactors_freeClosed {m : Nat} (AN f g : Fin m) : (copyFactors AN f g).FreeClosed := by
  simp -implicitDefEqProofs [copyFactors, Definitional.Formula.FreeClosed, ProjectSyntax.freeClosed]

theorem copyFactors_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (AN f g : Fin m) :
    Project.Formula.satisfies env (copyFactors AN f g) ↔ CopyFactors (env.bound AN) (env.bound f) (env.bound g) := by
  simp only [copyFactors, CopyFactors, Project.Formula.satisfies_forall_iff, Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_exists_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    KuratowskiZF.source_edge, ForcingDiagramOrder.product_semantics (M := M)]
  rfl

def copyCommon {m : Nat} (D N L A AN g : Fin m) : Project.Formula 1 m :=
  (.forallE (.forallE (.forallE (.forallE (.forallE (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge
  g.succ.succ.succ.succ.succ 4 2)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge
  g.succ.succ.succ.succ.succ 3 1)) (.imp (ConstructionMergerCopyCones.reaches N.succ.succ.succ.succ.succ
  AN.succ.succ.succ.succ.succ 2 0) (.imp (ConstructionMergerCopyCones.reaches N.succ.succ.succ.succ.succ
  AN.succ.succ.succ.succ.succ 1 0) (.existsE (.existsE (.conj (.mem (.bound 1) (.bound
  L.succ.succ.succ.succ.succ.succ.succ)) (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge
  g.succ.succ.succ.succ.succ.succ.succ 1 0)) (.conj (ConstructionMergerCopyCones.reaches
  D.succ.succ.succ.succ.succ.succ.succ A.succ.succ.succ.succ.succ.succ.succ 6 1) (.conj
  (ConstructionMergerCopyCones.reaches D.succ.succ.succ.succ.succ.succ.succ A.succ.succ.succ.succ.succ.succ.succ 5
  1) (ConstructionMergerCopyCones.reaches N.succ.succ.succ.succ.succ.succ.succ
  AN.succ.succ.succ.succ.succ.succ.succ 0 2))))))))))))))))

theorem copyCommon_freeClosed {m : Nat} (D N L A AN g : Fin m) : (copyCommon D N L A AN g).FreeClosed := by
  simp -implicitDefEqProofs [copyCommon, Definitional.Formula.FreeClosed, ProjectSyntax.freeClosed,
    ConstructionMergerCopyCones.reaches_freeClosed]

theorem copyCommon_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (D N L A AN g : Fin m) :
    Project.Formula.satisfies env (copyCommon D N L A AN g) ↔ CopyCommon (env.bound D) (env.bound N) (env.bound L) (env.bound A) (env.bound AN) (env.bound g) := by
  simp only [copyCommon, CopyCommon, Project.Formula.satisfies_forall_iff, Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_exists_iff, Project.Formula.satisfies_conj_iff, Project.Formula.satisfies_mem_iff,
    Project.Term.eval_bound, GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    KuratowskiZF.source_edge,
    ConstructionMergerCopyCones.reaches_semantics hM]
  rfl

def laws {m : Nat} (D N L LN projection projectionN A AN f g : Fin m) : Project.Formula 1 m :=
  (.conj (ProjectSyntax.encode id (Source.SetLanguage.injection g L LN)) (.conj
  (ConstructionProbeLettersMapSyntax.graph L projection projectionN f g) (.conj
  (ConstructionProbeLettersMapSyntax.representativeLaw projection projectionN f g) (.conj
  (ConstructionMergerEvaluation.equivariant A f g AN) (.conj (copyFactors AN f g) (copyCommon D N L A AN g))))))

theorem laws_freeClosed {m : Nat} (D N L LN projection projectionN A AN f g : Fin m) : (laws D N L LN projection projectionN A AN f g).FreeClosed := by
  simp -implicitDefEqProofs [laws, Definitional.Formula.FreeClosed, ProjectSyntax.freeClosed,
    ConstructionProbeLettersMapSyntax.graph_freeClosed, ConstructionProbeLettersMapSyntax.representativeLaw_freeClosed,
    ConstructionMergerEvaluation.equivariant_freeClosed, copyFactors_freeClosed, copyCommon_freeClosed]

theorem laws_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (D N L LN projection projectionN A AN f g : Fin m) :
    Project.Formula.satisfies env (laws D N L LN projection projectionN A AN f g) ↔
      Laws (env.bound D) (env.bound N) (env.bound L) (env.bound LN) (env.bound projection) (env.bound projectionN) (env.bound A) (env.bound AN) (env.bound f) (env.bound g) := by
  simp only [laws, Laws, Project.Formula.satisfies_conj_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingSupportSize.injection_semantics (M := M),
    ConstructionProbeLettersMapSyntax.graph_semantics hM,
    ConstructionProbeLettersMapSyntax.representativeLaw_semantics hM,
    ConstructionMergerEvaluation.equivariant_semantics hM, copyFactors_semantics hM, copyCommon_semantics hM]
  rfl

/-- The copy map is constructed inside nativeZF; the two actual presentations
are supplied by the already certified MergerPushout producers. -/
def sourceSentence {m : Nat} (w n zero D mul e P C L projection A W T B G unit O roots N mulN eN PN CN LN projectionN AN WN TN BN GN unitN ON rootsN f : Fin m) : Project.Sentence where
  formula := Project.Formula.forallClosure m
    (.imp (ConstructionMergerPushout.presentation w n zero D mul e P C L projection A W T B G unit O roots) (.imp
    (ConstructionMergerPushout.presentation w n zero N mulN eN PN CN LN projectionN AN WN TN BN GN unitN ON rootsN)
    (.imp (ConstructionProbeConservativeSyntax.conservative D N mul mulN f) (.imp
    (ConstructionProbeLiftHomSyntax.preservesProducts mul mulN f) (.imp
    (ConstructionMergerPrescriptionMapSyntax.mapped P f PN) (.imp
    (ConstructionProbeSharedIntersections.conditionalJoins D mul) (.existsE (laws D.succ N.succ L.succ LN.succ
    projection.succ projectionN.succ A.succ AN.succ f.succ 0))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,
      ConstructionMergerPushout.presentation_freeClosed,
      ConstructionProbeConservativeSyntax.conservative_freeClosed,
      ConstructionProbeLiftHomSyntax.preservesProducts_freeClosed,
      ConstructionMergerPrescriptionMapSyntax.mapped_freeClosed,
      ConstructionProbeSharedIntersections.conditionalJoins_freeClosed, laws_freeClosed]

theorem source_models {m : Nat} (w n zero D mul e P C L projection A W T B G unit O roots N mulN eN PN CN LN projectionN AN WN TN BN GN unitN ON rootsN f : Fin m) (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (sourceSentence w n zero D mul e P C L projection A W T B G unit O roots N mulN eN PN CN LN projectionN AN WN TN BN GN unitN ON rootsN f)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) (sourceSentence w n zero D mul e P C L projection A W T B G unit O roots N mulN eN PN CN LN projectionN AN WN TN BN GN unitN ON rootsN f)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff, Project.Formula.satisfies_exists_iff,
    ConstructionMergerPushout.presentation_semantics hM,
    ConstructionProbeConservativeSyntax.conservative_semantics hM,
    ConstructionProbeLiftHomSyntax.preservesProducts_semantics hM,
    ConstructionMergerPrescriptionMapSyntax.mapped_semantics hM,
    ConstructionProbeSharedIntersections.conditionalJoins_semantics hM, laws_semantics hM]
  exact exists_system hM

theorem source_kernel_certificate {m : Nat} (w n zero D mul e P C L projection A W T B G unit O roots N mulN eN PN CN LN projectionN AN WN TN BN GN unitN ON rootsN f : Fin m) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (sourceSentence w n zero D mul e P C L projection A W T B G unit O roots N mulN eN PN CN LN projectionN AN WN TN BN GN unitN ON rootsN f)) :=
  ModelTransfer.derives (fun _ hM => source_models w n zero D mul e P C L projection A W T B G unit O roots N mulN eN PN CN LN projectionN AN WN TN BN GN unitN ON rootsN f hM)

end PPAC.Migration.ConstructionMergerCopiesMap
