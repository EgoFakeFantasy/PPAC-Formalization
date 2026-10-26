/- Pinned ProbeWords.Path cone laws. Consumers: ProbeWords old divisibility,
ProbeMargins, ProbePresentations and the initial probe generator. -/
import PPAC.Migration.ConstructionProbeAlphabet

namespace PPAC.Migration.ConstructionProbeCones
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ForcingDiagramOrder (Product product product_semantics)
open ForcingDiagramPoset (LeftCancelMonoid)
open ForcingSupportSize (MapsTo)
open ConstructionBaseMonoid (Divides divides divides_semantics)
open ConstructionProbePath
open ConstructionProbeLetters
open ConstructionProbeAction
open ConstructionProbeTransitions (Transition product_closed transition_closed)
open ConstructionProbeAlphabet (InCone inCone inCone_freeClosed inCone_semantics)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def FiniteCone (w D mul F b i y : M.Carrier .set) : Prop :=
  ∃ j z, (Project.FirstOrderSemantics.reduct M).mem j w ∧
    Transition D mul F i j y z ∧ Divides D mul b z

theorem inCone_letter_iff (hM : FirstOrder.Theory.Models M nativeZF)
    {w D mul e node F C L projection A b i y c : M.Carrier .set}
    (hm : LeftCancelMonoid D mul e) (hF : FactorTable w D mul node F)
    (hC : Representatives w D C) (hp : MapsTo C L projection)
    (hE : EqualityLaw w D mul F projection) (hMeets : ConstructionProbeTransitions.MeetsLaws w D mul F)
    (hA : ActionTable D mul projection A) (hb : (Project.FirstOrderSemantics.reduct M).mem b D)
    (hiy : Product projection i y c) : InCone L A b c ↔ FiniteCone w D mul F b i y := by
  constructor
  · rintro ⟨t,_,hact⟩
    obtain ⟨_,j,x,bx,hx,hxt,hbx,hbxc⟩ := (hA b t c).mp hact
    obtain ⟨k,z,hk,hyz,hbxz⟩ := (letter_eq_iff hE hiy hbxc).mp rfl
    obtain ⟨_,f,hf,hbxf⟩ := hbxz
    obtain ⟨_,_,_,ni,nk,_,_,hfD,_⟩ := (hF j k f).mp hf
    obtain ⟨xf,hxfD,hxf⟩ := (hm.2.1 x hx).1 f hfD
    exact ⟨k,z,hk,hyz,xf,hxfD,(hm.2.2 b x f bx xf z hb hx hfD hbx hxf).mp hbxf⟩
  · rintro ⟨j,z,hj,hyz,v,hv,hbv⟩
    obtain ⟨t,ht,hvt⟩ := projected hM hC hp hj hv
    obtain ⟨s,_,hzs⟩ := projected hM hC hp hj (transition_closed hm hF hyz)
    have hcs := letter_transition hMeets hE hyz hiy hzs
    exact ⟨t,ht,(hA b t c).mpr ⟨hb,j,v,z,hv,hvt,hbv,hcs.symm ▸ hzs⟩⟩

theorem one_inCone {mul e L A c : M.Carrier .set} (hA : ActionLaws mul e L A)
    (hc : (Project.FirstOrderSemantics.reduct M).mem c L) : InCone L A e c := ⟨c,hc,hA.1 c hc⟩

theorem inCone_of_dvd (hM : FirstOrder.Theory.Models M nativeZF)
    {w D mul e node F C L projection A x y c : M.Carrier .set}
    (hm : LeftCancelMonoid D mul e) (hF : FactorTable w D mul node F)
    (hC : Representatives w D C) (hL : Letters w D mul F C L)
    (hp : MapsTo C L projection) (hProjection : Projection w D mul F C projection)
    (hE : EqualityLaw w D mul F projection) (hA : ActionTable D mul projection A)
    (hx : (Project.FirstOrderSemantics.reduct M).mem x D)
    (hxy : Divides D mul x y) (hyc : InCone L A y c) : InCone L A x c := by
  obtain ⟨v,hv,hxv⟩ := hxy
  obtain ⟨t,ht,hyt⟩ := hyc
  obtain ⟨s,hs,hvs⟩ := act_total hM hm hC hL hp hProjection hv ht
  obtain ⟨q,_,hxq⟩ := act_total hM hm hC hL hp hProjection hx hs
  have hyq := act_mul hM hm hF hC hp hE hxv hvs hxq
  have hqc := act_unique hm hF hE hyq ((hA y t c).mp hyt)
  exact ⟨s,hs,(hA x s c).mpr (hqc ▸ hxq)⟩

def JoinProperty (D mul x y j : M.Carrier .set) : Prop := ∀ z,
  (Project.FirstOrderSemantics.reduct M).mem z D →
    (Divides D mul x z ∧ Divides D mul y z ↔ Divides D mul j z)

theorem inCone_intersection (hM : FirstOrder.Theory.Models M nativeZF)
    {w D mul e node F C L projection A x y j c : M.Carrier .set}
    (hm : LeftCancelMonoid D mul e) (hF : FactorTable w D mul node F)
    (hC : Representatives w D C) (hL : Letters w D mul F C L)
    (hp : MapsTo C L projection) (hProjection : Projection w D mul F C projection)
    (hE : EqualityLaw w D mul F projection) (hMeets : ConstructionProbeTransitions.MeetsLaws w D mul F)
    (hA : ActionTable D mul projection A)
    (hx : (Project.FirstOrderSemantics.reduct M).mem x D)
    (hy : (Project.FirstOrderSemantics.reduct M).mem y D)
    (hj : (Project.FirstOrderSemantics.reduct M).mem j D)
    (hJoin : JoinProperty D mul x y j) : InCone L A x c ∧ InCone L A y c ↔ InCone L A j c := by
  constructor
  · rintro ⟨⟨t,_,hxt⟩,⟨v,_,hyv⟩⟩
    obtain ⟨_,i,u,xu,hu,hut,hxu,hxuc⟩ := (hA x t c).mp hxt
    obtain ⟨_,l,r,yr,hr,hrv,hyr,hyrc⟩ := (hA y v c).mp hyv
    obtain ⟨k,z,hk,hxz,hyz⟩ := (letter_eq_iff hE hxuc hyrc).mp rfl
    have hzD := transition_closed hm hF hxz
    have hzdiv : Divides D mul x z ∧ Divides D mul y z := by
      obtain ⟨_,f,hf,hxf⟩ := hxz
      obtain ⟨_,g,hg,hyg⟩ := hyz
      obtain ⟨_,_,_,ni,nk,_,_,hfD,_⟩ := (hF i k f).mp hf
      obtain ⟨_,_,_,nl,nk',_,_,hgD,_⟩ := (hF l k g).mp hg
      obtain ⟨uf,hufD,huf⟩ := (hm.2.1 u hu).1 f hfD
      obtain ⟨rg,hrgD,hrg⟩ := (hm.2.1 r hr).1 g hgD
      exact ⟨⟨uf,hufD,(hm.2.2 x u f xu uf z hx hu hfD hxu huf).mp hxf⟩,
        ⟨rg,hrgD,(hm.2.2 y r g yr rg z hy hr hgD hyr hrg).mp hyg⟩⟩
    obtain ⟨r,hr,hjr⟩ := (hJoin z hzD).mp hzdiv
    obtain ⟨t,ht,hrt⟩ := projected hM hC hp hk hr
    obtain ⟨q,_,hzq⟩ := projected hM hC hp hk hzD
    have hcq := letter_transition hMeets hE hxz hxuc hzq
    exact ⟨t,ht,(hA j t c).mpr ⟨hj,k,r,z,hr,hrt,hjr,hcq.symm ▸ hzq⟩⟩
  · intro hjc
    have hjj : Divides D mul j j := ⟨e,hm.1.1,(hm.1.2 j hj j).2.mpr rfl⟩
    have hxy := (hJoin j hj).mpr hjj
    exact ⟨inCone_of_dvd hM hm hF hC hL hp hProjection hE hA hx hxy.1 hjc,
      inCone_of_dvd hM hm hF hC hL hp hProjection hE hA hy hxy.2 hjc⟩

theorem old_common_multiple_of_cones {D mul e L I A K projection T x y c : M.Carrier .set}
    (hm : LeftCancelMonoid D mul e) (hI : Representatives D L I) (hA : MapsTo I L A)
    (hK : MapsTo L D K) (hLaws : ConstructionProbeTarget.TargetLaws mul projection T A K)
    (hc : (Project.FirstOrderSemantics.reduct M).mem c L) (hx : InCone L A x c) (hy : InCone L A y c) :
    ∃ z, (Project.FirstOrderSemantics.reduct M).mem z D ∧ Divides D mul x z ∧ Divides D mul y z := by
  obtain ⟨z,hz,_⟩ := hK.1.2 c hc
  exact ⟨z,hK.2 c z hz,ConstructionProbeAlphabet.dvd_target_of_inCone hm hI hA hK hLaws hx hz,
    ConstructionProbeAlphabet.dvd_target_of_inCone hm hI hA hK hLaws hy hz⟩

def InitialProfile (w D mul node b : M.Carrier .set) : Prop := ∃ i n,
  (Project.FirstOrderSemantics.reduct M).mem i w ∧ PureKuratowski.PairMember M i n node ∧ Divides D mul b n

theorem initial_profile (hM : FirstOrder.Theory.Models M nativeZF)
    {w D mul e zero a node F T C L projection A b c : M.Carrier .set}
    (hm : LeftCancelMonoid D mul e) (hPath : Path w D mul e zero a node)
    (hF : FactorTable w D mul node F) (hTable : TableLaws w mul e zero a node F T)
    (hC : Representatives w D C) (hp : MapsTo C L projection)
    (hE : EqualityLaw w D mul F projection) (hMeets : ConstructionProbeTransitions.MeetsLaws w D mul F)
    (hA : ActionTable D mul projection A) (hb : (Project.FirstOrderSemantics.reduct M).mem b D)
    (hzero : Product projection zero e c) : InCone L A b c ↔ InitialProfile w D mul node b := by
  rw [inCone_letter_iff hM hm hF hC hp hE hMeets hA hb hzero]
  constructor
  · rintro ⟨i,z,hi,⟨_,f,hf,hef⟩,hbz⟩
    obtain ⟨n,hin,_⟩ := hPath.1.1.2 i hi
    have hfn := hTable.2.1 i n hi hin
    have hfe := factor_unique hm hPath.1 ((hF zero i f).mp hf).2.2.2 ((hF zero i n).mp hfn).2.2.2
    subst f
    have hzn := (hm.1.2 n (hPath.1.2 i n hin) z).1.mp hef
    exact ⟨i,n,hi,hin,hzn ▸ hbz⟩
  · rintro ⟨i,n,hi,hin,hbn⟩
    exact ⟨i,n,hi,⟨hm.1.1,n,hTable.2.1 i n hi hin,
      (hm.1.2 n (hPath.1.2 i n hin) n).1.mpr rfl⟩,hbn⟩

def ConeLaws (w D mul e zero node F L projection A : M.Carrier .set) : Prop :=
  (∀ b i y c, (Project.FirstOrderSemantics.reduct M).mem b D → Product projection i y c →
    (InCone L A b c ↔ FiniteCone w D mul F b i y)) ∧
  (∀ c, (Project.FirstOrderSemantics.reduct M).mem c L → InCone L A e c) ∧
  (∀ x y c, (Project.FirstOrderSemantics.reduct M).mem x D → Divides D mul x y →
    InCone L A y c → InCone L A x c) ∧
  (∀ x y j c, (Project.FirstOrderSemantics.reduct M).mem x D →
    (Project.FirstOrderSemantics.reduct M).mem y D → (Project.FirstOrderSemantics.reduct M).mem j D →
    JoinProperty D mul x y j → (InCone L A x c ∧ InCone L A y c ↔ InCone L A j c)) ∧
  (∀ x y c, (Project.FirstOrderSemantics.reduct M).mem c L → InCone L A x c → InCone L A y c →
    ∃ z, (Project.FirstOrderSemantics.reduct M).mem z D ∧ Divides D mul x z ∧ Divides D mul y z) ∧
  (∀ b c, (Project.FirstOrderSemantics.reduct M).mem b D → Product projection zero e c →
    (InCone L A b c ↔ InitialProfile w D mul node b))

theorem cone_laws (hM : FirstOrder.Theory.Models M nativeZF)
    {w D mul e zero a node F T C L projection I A K : M.Carrier .set}
    (hm : LeftCancelMonoid D mul e) (hPath : Path w D mul e zero a node)
    (hF : FactorTable w D mul node F) (hTable : TableLaws w mul e zero a node F T)
    (hC : Representatives w D C) (hL : Letters w D mul F C L)
    (hp : MapsTo C L projection) (hProjection : Projection w D mul F C projection)
    (hE : EqualityLaw w D mul F projection) (hMeets : ConstructionProbeTransitions.MeetsLaws w D mul F)
    (hI : Representatives D L I) (hAMap : MapsTo I L A) (hA : ActionTable D mul projection A)
    (hAction : ActionLaws mul e L A) (hK : MapsTo L D K)
    (hTarget : ConstructionProbeTarget.TargetLaws mul projection T A K) :
    ConeLaws w D mul e zero node F L projection A := by
  exact ⟨fun _ _ _ _ hb hc => inCone_letter_iff hM hm hF hC hp hE hMeets hA hb hc,
    fun _ hc => one_inCone hAction hc,
    fun _ _ _ hx hxy hyc => inCone_of_dvd hM hm hF hC hL hp hProjection hE hA hx hxy hyc,
    fun _ _ _ _ hx hy hj hJoin => inCone_intersection hM hm hF hC hL hp hProjection hE hMeets hA hx hy hj hJoin,
    fun _ _ _ hc hx hy => old_common_multiple_of_cones hm hI hAMap hK hTarget hc hx hy,
    fun _ _ hb hc => initial_profile hM hm hPath hF hTable hC hp hE hMeets hA hb hc⟩

def finiteCone {m : Nat} (w D mul F b i y : Fin m) : Project.Formula 1 m :=
  (.existsE (.existsE (.conj (.mem (.bound 1) (.bound w.succ.succ)) (.conj
    (ConstructionProbeTransitions.transition D.succ.succ mul.succ.succ F.succ.succ i.succ.succ 1 y.succ.succ 0)
    (ProjectSyntax.encode id (divides D.succ.succ mul.succ.succ b.succ.succ 0))))))

theorem finiteCone_freeClosed {m : Nat} (w D mul F b i y : Fin m) : (finiteCone w D mul F b i y).FreeClosed := by
  simp -implicitDefEqProofs [finiteCone,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,ConstructionProbeTransitions.transition_freeClosed]

theorem finiteCone_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w D mul F b i y : Fin m) :
    Project.Formula.satisfies env (finiteCone w D mul F b i y) ↔
      FiniteCone (env.bound w) (env.bound D) (env.bound mul) (env.bound F) (env.bound b) (env.bound i) (env.bound y) := by
  simp only [finiteCone,
    FiniteCone,
    Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_mem_iff,
    Project.Term.eval_bound,
    ConstructionProbeTransitions.transition_semantics hM,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    divides_semantics (M := M)]
  rfl

def joinProperty {m : Nat} (D mul x y j : Fin m) : Project.Formula 1 m :=
  (.forallE (.imp (.mem (.bound 0) (.bound D.succ)) (.iff (.conj (ProjectSyntax.encode id (divides D.succ
    mul.succ x.succ 0)) (ProjectSyntax.encode id (divides D.succ mul.succ y.succ 0))) (ProjectSyntax.encode id
    (divides D.succ mul.succ j.succ 0)))))

theorem joinProperty_freeClosed {m : Nat} (D mul x y j : Fin m) : (joinProperty D mul x y j).FreeClosed := by
  simp -implicitDefEqProofs [joinProperty,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed]

theorem joinProperty_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (D mul x y j : Fin m) :
    Project.Formula.satisfies env (joinProperty D mul x y j) ↔
      JoinProperty (env.bound D) (env.bound mul) (env.bound x) (env.bound y) (env.bound j) := by
  simp only [joinProperty,
    JoinProperty,
    Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_mem_iff,
    Project.Term.eval_bound,
    Project.Formula.satisfies_iff_iff,
    Project.Formula.satisfies_conj_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    divides_semantics (M := M)]
  rfl

def initialProfile {m : Nat} (w D mul node b : Fin m) : Project.Formula 1 m :=
  (.existsE (.existsE (.conj (.mem (.bound 1) (.bound w.succ.succ)) (.conj (ProjectSyntax.encode id
    (Source.SetLanguage.edge node.succ.succ 1 0)) (ProjectSyntax.encode id (divides D.succ.succ mul.succ.succ
    b.succ.succ 0))))))

theorem initialProfile_freeClosed {m : Nat} (w D mul node b : Fin m) : (initialProfile w D mul node b).FreeClosed := by
  simp -implicitDefEqProofs [initialProfile,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed]

theorem initialProfile_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w D mul node b : Fin m) :
    Project.Formula.satisfies env (initialProfile w D mul node b) ↔
      InitialProfile (env.bound w) (env.bound D) (env.bound mul) (env.bound node) (env.bound b) := by
  simp only [initialProfile,
    InitialProfile,
    Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_mem_iff,
    Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    KuratowskiZF.source_edge,
    divides_semantics (M := M)]
  rfl

def coneLaws {m : Nat} (w D mul e zero node F L projection A : Fin m) : Project.Formula 1 m :=
  (.conj (.forallE (.forallE (.forallE (.forallE (.imp (.mem (.bound 3) (.bound D.succ.succ.succ.succ)) (.imp
    (ProjectSyntax.encode id (product projection.succ.succ.succ.succ 2 1 0)) (.iff (inCone L.succ.succ.succ.succ
    A.succ.succ.succ.succ 3 0) (finiteCone w.succ.succ.succ.succ D.succ.succ.succ.succ mul.succ.succ.succ.succ
    F.succ.succ.succ.succ 3 2 1)))))))) (.conj (.forallE (.imp (.mem (.bound 0) (.bound L.succ)) (inCone L.succ
    A.succ e.succ 0))) (.conj (.forallE (.forallE (.forallE (.imp (.mem (.bound 2) (.bound D.succ.succ.succ))
    (.imp (ProjectSyntax.encode id (divides D.succ.succ.succ mul.succ.succ.succ 2 1)) (.imp (inCone
    L.succ.succ.succ A.succ.succ.succ 1 0) (inCone L.succ.succ.succ A.succ.succ.succ 2 0))))))) (.conj (.forallE
    (.forallE (.forallE (.forallE (.imp (.mem (.bound 3) (.bound D.succ.succ.succ.succ)) (.imp (.mem (.bound 2)
    (.bound D.succ.succ.succ.succ)) (.imp (.mem (.bound 1) (.bound D.succ.succ.succ.succ)) (.imp (joinProperty
    D.succ.succ.succ.succ mul.succ.succ.succ.succ 3 2 1) (.iff (.conj (inCone L.succ.succ.succ.succ
    A.succ.succ.succ.succ 3 0) (inCone L.succ.succ.succ.succ A.succ.succ.succ.succ 2 0)) (inCone
    L.succ.succ.succ.succ A.succ.succ.succ.succ 1 0)))))))))) (.conj (.forallE (.forallE (.forallE (.imp (.mem
    (.bound 0) (.bound L.succ.succ.succ)) (.imp (inCone L.succ.succ.succ A.succ.succ.succ 2 0) (.imp (inCone
    L.succ.succ.succ A.succ.succ.succ 1 0) (.existsE (.conj (.mem (.bound 0) (.bound D.succ.succ.succ.succ))
    (.conj (ProjectSyntax.encode id (divides D.succ.succ.succ.succ mul.succ.succ.succ.succ 3 0))
    (ProjectSyntax.encode id (divides D.succ.succ.succ.succ mul.succ.succ.succ.succ 2 0))))))))))) (.forallE
    (.forallE (.imp (.mem (.bound 1) (.bound D.succ.succ)) (.imp (ProjectSyntax.encode id (product
    projection.succ.succ zero.succ.succ e.succ.succ 0)) (.iff (inCone L.succ.succ A.succ.succ 1 0)
    (initialProfile w.succ.succ D.succ.succ mul.succ.succ node.succ.succ 1)))))))))))

theorem coneLaws_freeClosed {m : Nat} (w D mul e zero node F L projection A : Fin m) :
    (coneLaws w D mul e zero node F L projection A).FreeClosed := by
  simp -implicitDefEqProofs [coneLaws,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
    inCone_freeClosed,finiteCone_freeClosed,joinProperty_freeClosed,initialProfile_freeClosed]

theorem coneLaws_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w D mul e zero node F L projection A : Fin m) :
    Project.Formula.satisfies env (coneLaws w D mul e zero node F L projection A) ↔
      ConeLaws (env.bound w) (env.bound D) (env.bound mul) (env.bound e) (env.bound zero) (env.bound node) (env.bound F) (env.bound L) (env.bound projection) (env.bound A) := by
  simp only [coneLaws,ConeLaws,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_iff_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),product_semantics (M := M),
    divides_semantics (M := M),inCone_semantics hM,finiteCone_semantics hM,joinProperty_semantics hM,
    initialProfile_semantics hM]
  rfl

def constructionSentence : Project.Sentence where
  formula := (Project.Formula.forallClosure 7 (.imp (Project.Formula.isOmega (.bound 0)) (.imp (.forallE (.neg (.mem (.bound
    0) (.bound 5)))) (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid (1 : Fin 7) 2 3))
    (.imp (path (0 : Fin 7) 1 2 3 4 5 6) (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE
    (.existsE (.existsE (.conj (factorTable (9 : Fin 16) 10 11 15 8) (.conj (terminalTable (9 : Fin 16) 10 11 15
    14 7) (.conj (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (7 : Fin 16) 9 10)) (.conj (representatives
    (9 : Fin 16) 10 6) (.conj (letters (9 : Fin 16) 10 11 8 6 5) (.conj (ProjectSyntax.encode id
    (Source.SetLanguage.mapsTo (4 : Fin 16) 6 5)) (.conj (projectionGraph (9 : Fin 16) 10 11 8 6 4) (.conj
    (equalityLaw (9 : Fin 16) 10 11 8 4) (.conj (representatives (10 : Fin 16) 5 3) (.conj (ProjectSyntax.encode
    id (Source.SetLanguage.mapsTo (2 : Fin 16) 3 5)) (.conj (actionTable (10 : Fin 16) 11 4 2) (.conj
    (actionLaws (11 : Fin 16) 12 5 2) (.conj (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (1 : Fin 16) 5
    10)) (.conj (ConstructionProbeTarget.targetGraph (10 : Fin 16) 11 4 7 1) (.conj
    (ConstructionProbeTarget.targetLaws (11 : Fin 16) 4 7 2 1) (.conj (.mem (.bound 0) (.bound 5)) (.conj
    (ProjectSyntax.encode id (product (4 : Fin 16) 13 12 0)) (coneLaws (9 : Fin 16) 10 11 12 13 15 8 5 4
    2))))))))))))))))))))))))))))))))
  freeClosed := by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
    path_freeClosed,factorTable_freeClosed,terminalTable_freeClosed,representatives_freeClosed,letters_freeClosed,
    projectionGraph_freeClosed,equalityLaw_freeClosed,actionTable_freeClosed,actionLaws_freeClosed,
    ConstructionProbeTarget.targetGraph_freeClosed,ConstructionProbeTarget.targetLaws_freeClosed,coneLaws_freeClosed]

theorem construction_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence constructionSentence).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) constructionSentence]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_isOmega_iff,Project.Term.eval_bound,
    Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_neg_iff,Project.Formula.satisfies_mem_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),path_semantics hM,
    Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,factorTable_semantics hM,
    terminalTable_semantics hM,representatives_semantics hM,letters_semantics hM,
    ForcingSupportSize.mapsTo_semantics (M := M),projectionGraph_semantics hM,equalityLaw_semantics hM,
    actionTable_semantics hM,actionLaws_semantics hM,ConstructionProbeTarget.targetGraph_semantics hM,
    ConstructionProbeTarget.targetLaws_semantics hM,product_semantics (M := M),coneLaws_semantics hM]
  intro hw hz hm hp
  obtain ⟨pairs,hpairs⟩ := exists_ordered_pairs hM (bound 0)
  obtain ⟨F,_,hF⟩ := exists_factor_table hM hm hp hpairs
  obtain ⟨T,hTm,hT⟩ := exists_terminal_table hM hm hp
  have hTable := table_laws hM hw hz hm hp hF hT
  have hMeets := ConstructionProbeTransitions.meets_laws hM hw hm hp hF hTable
  obtain ⟨C,hC⟩ := exists_representatives hM (bound 0) (bound 1)
  obtain ⟨L,hL⟩ := exists_letters hM (bound 0) (bound 1) (bound 2) F C
  obtain ⟨projection,hpMap,hProjection⟩ := exists_projection hM hL
  have hE := equality_law hM hC hMeets hProjection
  obtain ⟨I,A,hI,hA,hAction⟩ := exists_action hM hm hF hC hL hpMap hProjection hE
  have hALaws := action_laws hM hm hF hC hL hpMap hProjection hE hAction
  obtain ⟨K,hK,hTarget⟩ := ConstructionProbeTarget.exists_target hM hm hF hC hL hpMap hProjection hE hTm hTable
  have hKLaws := ConstructionProbeTarget.target_laws hm hF hC hpMap hE hTm hTable hAction hTarget
  have hzero := ForcingConditionGraphs.function_input hp.1.1 hp.2.2.1
  obtain ⟨q,hq,hqEq⟩ := projected hM hC hpMap hzero hm.1.1
  exact ⟨F,T,C,L,projection,I,A,K,q,hF,hT,hTm,hC,hL,hpMap,hProjection,hE,hI,hA,hAction,
    hALaws,hK,hTarget,hKLaws,hq,hqEq,
    cone_laws hM hm hp hF hTable hC hL hpMap hProjection hE hMeets hI hA hAction hALaws hK hKLaws⟩

theorem construction_kernel_certificate : FirstOrder.Derives nativeZF []
    (Project.fo_sentence constructionSentence) := ModelTransfer.derives (fun _ hM => construction_models hM)

end PPAC.Migration.ConstructionProbeCones
