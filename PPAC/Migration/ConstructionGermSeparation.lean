/- Pinned GermSelectors.TailData.detector_separates:459-478.
Consume the actual component stabilizer and existing detector graphs.
All indices and graph values range over the internal set universe. -/
import PPAC.Migration.ConstructionGermDetectors

namespace PPAC.Migration.ConstructionGermSeparation
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ForcingConditionGraphs (Permutation CompositionGraph InverseGraph function_input function_unique)
open ForcingSupportSize (Injection)
open ForcingComponentMove (Move)
open ConstructionCountableAlignments (Stabilizes)
open ConstructionGermCosets (Carrier Class Classes)
open ConstructionGermDetectors (Representatives Nonidentity Detectors)
open ConstructionComponentCofinal (Chain)
open ConstructionFractionOrder (NatLe)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

/-- Compose the existing diagram graphs, retaining their exact domain. -/
theorem compose_diagrams {D I pi sigma product r s t : M.Carrier .set}
    (hr : Injection D I r) (hmul : CompositionGraph I pi sigma product)
    (hfirst : CompositionGraph D sigma r s) (hsecond : CompositionGraph D pi s t) :
    CompositionGraph D product r t := by
  intro x z
  constructor
  · intro hxt
    obtain ⟨hx,y,hxy,hyz⟩ := (hsecond x z).mp hxt
    obtain ⟨_,a,hxa,hay⟩ := (hfirst x y).mp hxy
    exact ⟨hx,a,hxa,(hmul a z).mpr ⟨hr.1.2 x a hxa,y,hay,hyz⟩⟩
  · rintro ⟨hx,a,hxa,haz⟩
    obtain ⟨_,y,hay,hyz⟩ := (hmul a z).mp haz
    exact (hsecond x z).mpr ⟨hx,y,(hfirst x y).mpr ⟨hx,a,hxa,hay⟩,hyz⟩

theorem move_composition {D I mul q pi sigma product v V W : M.Carrier .set}
    (hmul : CompositionGraph I pi sigma product)
    (hfirst : Move D I mul q sigma v V) (hsecond : Move D I mul q pi V W) :
    Move D I mul q product v W := by
  obtain ⟨r,a,U,s,hv,hV,hr,_,hfirst⟩ := hfirst
  obtain ⟨s',a',U',t,hV',hW,_,ht,hsecond⟩ := hsecond
  obtain ⟨rfl,rfl,rfl⟩ := ConstructionComponentCarrier.code_injective hV hV'
  exact ⟨r,a,U,t,hv,hW,hr,ht,compose_diagrams hr.1 hmul hfirst hsecond⟩

theorem stabilizes_inverse (hM : FirstOrder.Theory.Models M nativeZF)
    {D I mul q root pi inv : M.Carrier .set} (hq : Injection D I q)
    (hp : Stabilizes D I mul q root pi) (hi : Permutation I inv) (hInv : InverseGraph pi inv) :
    Stabilizes D I mul q root inv := by
  obtain ⟨v,hv,hCommon⟩ := hp.2.2
  have hFix := ForcingDiagramCarrier.reverse hp.1 hq hInv hp.2.1
  obtain ⟨V,hV⟩ := ForcingComponentMove.exists_move hM hi hFix (ForcingComponentMove.source_vertex hv)
  have hBack := ForcingComponentMove.move_inverse hp.1 hInv hv
  exact ⟨hi,hFix,V,hV,ForcingComponentRebase.common_symm
    (ForcingComponentMove.move_common hM hi hFix hV hBack hCommon)⟩

theorem stabilizes_composition (hM : FirstOrder.Theory.Models M nativeZF)
    {D I mul unit q root pi sigma product : M.Carrier .set}
    (hm : ForcingDiagramPoset.LeftCancelMonoid D mul unit)
    (hJ : ConstructionProbeSharedIntersections.ConditionalJoins D mul)
    (hq : Injection D I q) (hp : Stabilizes D I mul q root pi)
    (hs : Stabilizes D I mul q root sigma) (ht : Permutation I product)
    (hmul : CompositionGraph I pi sigma product) : Stabilizes D I mul q root product := by
  obtain ⟨v,hv,hCommonV⟩ := hs.2.2
  obtain ⟨u,hu,hCommonU⟩ := hp.2.2
  obtain ⟨t,hvt⟩ := ForcingComponentMove.exists_move hM hp.1 hp.2.1 (ForcingComponentMove.target_vertex hv)
  have hut := ForcingComponentMove.move_common hM hp.1 hp.2.1 hu hvt hCommonV
  exact ⟨ht,compose_diagrams hq hmul hs.2.1 hp.2.1,t,move_composition hmul hv hvt,
    ForcingComponentGluing.common_between hM hm hJ (ForcingComponentRebase.common_symm hCommonU) hut⟩

/-- One nonidentity coset separates the two actions at every sufficiently
late internal natural index, not merely at one selected detector point. -/
def Separates (w N det g h : M.Carrier .set) : Prop :=
  ∃ delta bound, (Project.FirstOrderSemantics.reduct M).mem delta N ∧
    (Project.FirstOrderSemantics.reduct M).mem bound w ∧ ∀ n,
      (Project.FirstOrderSemantics.reduct M).mem n w → NatLe bound n →
      ∃ p x y z, PureKuratowski.Code M p delta n ∧ PureKuratowski.PairMember M p x det ∧
        PureKuratowski.PairMember M x y g ∧ PureKuratowski.PairMember M x z h ∧ y ≠ z

theorem detector_separates (hM : FirstOrder.Theory.Models M nativeZF)
    {w D I mul unit q zero root vertices chain H Q reps N X det g h C E : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hm : ForcingDiagramPoset.LeftCancelMonoid D mul unit)
    (hJ : ConstructionProbeSharedIntersections.ConditionalJoins D mul)
    (hq : Injection D I q) (hChain : Chain w D I mul q zero root vertices chain)
    (hH : Carrier D I mul q root H) (hQ : Classes w D chain H Q)
    (hReps : Representatives H Q reps) (hN : Nonidentity w D chain Q reps N)
    (hDet : Detectors D I chain X reps det)
    (hX : (Project.FirstOrderSemantics.reduct M).IsCartesianProduct (KuratowskiZF.interpretation hM) X N w)
    (hg : (Project.FirstOrderSemantics.reduct M).mem g H)
    (hh : (Project.FirstOrderSemantics.reduct M).mem h H)
    (hC : Class w D chain H g C) (hE : Class w D chain H h E) (hne : C ≠ E) :
    Separates w N det g h := by
  have hgp := (hH g).mp hg
  have hhp := (hH h).mp hh
  obtain ⟨inv,hi,hInv⟩ := ForcingConditionGraphs.exists_inverse hM hgp.1
  obtain ⟨diff,hd,hComp⟩ := ForcingConditionGraphs.exists_composition hM hi hhp.1
  have hInvS := stabilizes_inverse hM hq hgp hi hInv
  have hDiff := stabilizes_composition hM hm hJ hq hInvS hhp hd hComp
  have hdH := (hH diff).mpr hDiff
  obtain ⟨delta,hClass⟩ := ConstructionGermCosets.exists_class hM w D chain H diff
  have hdQ := (hQ delta).mpr ⟨diff,hdH,hClass⟩
  have hdN := (ConstructionGermDetectors.nonidentity_iff hM hw hChain hReps hN hdQ hClass).mpr
    (fun hFix => hne (ConstructionGermCosets.class_eq_of_same hM hw hChain hC hE
      ((ConstructionGermCosets.same_iff_tail hChain hgp.1 hhp.1 hInv hComp).mpr hFix)))
  obtain ⟨rep,hRep,_⟩ := hReps.1.1.2 delta hdQ
  have hSame := ((hClass rep).mp (hReps.2 delta rep hRep)).2
  obtain ⟨bound,hbound,hAgree⟩ := ConstructionGermDetectors.same_eventually hChain hDet hSame
  refine ⟨delta,bound,hdN,hbound,?_⟩
  intro n hn hbn
  obtain ⟨p,hp⟩ := KuratowskiZF.exists_code hM delta n
  have hpX := (hX p).mpr ⟨delta,hdN,n,hn,hp⟩
  obtain ⟨x,hx,_⟩ := hDet.1.1.2 p hpX
  have hxI := hDet.1.2 p x hx
  obtain ⟨y,hxy,_⟩ := hgp.1.1.1.2 x hxI
  obtain ⟨z,hxz,_⟩ := hhp.1.1.1.2 x hxI
  refine ⟨p,x,y,z,hp,hx,hxy,hxz,?_⟩
  intro heq
  subst z
  obtain ⟨delta',n',rep',v,hp',hRep',_,hxv,hneV⟩ := hDet.2 p x hx
  obtain ⟨rfl,rfl⟩ := PureKuratowski.code_injective hp hp'
  have heRep := function_unique hReps.1.1 hRep' hRep
  subst rep'
  have hdxx := (hComp x x).mpr ⟨hDet.1.2 p x hx,y,hxz,(hInv x y).mp hxy⟩
  have hdxv := (hAgree delta n p x v hp hx hbn).mpr hxv
  exact hneV (function_unique hd.1.1 hdxv hdxx)

def separates {m : Nat} (w N det g h : Fin m) : Project.Formula 1 m :=
  (.existsE (.existsE (.conj (.mem (.bound 1) (.bound N.succ.succ)) (.conj (.mem (.bound 0) (.bound w.succ.succ)) (.forallE (.imp (.mem (.bound 0) (.bound w.succ.succ.succ)) (.imp (.disj (Project.Formula.extensionalEq (.bound 1) (.bound 0)) (.mem (.bound 1) (.bound 0))) (.existsE (.existsE (.existsE (.existsE (.conj (PureKuratowskiProject.code (.bound 3) (.bound 6) (.bound 4)) (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge det.succ.succ.succ.succ.succ.succ.succ 3 2)) (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge g.succ.succ.succ.succ.succ.succ.succ 2 1)) (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge h.succ.succ.succ.succ.succ.succ.succ 2 0)) (.neg (Project.Formula.extensionalEq (.bound 1) (.bound 0))))))))))))))))))

theorem separates_freeClosed {m : Nat} (w N det g h : Fin m) : (separates w N det g h).FreeClosed := by
  simp -implicitDefEqProofs [separates,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
    PureKuratowskiProject.code,Project.Formula.extensionalEq]

theorem separates_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w N det g h : Fin m) :
    Project.Formula.satisfies env (separates w N det g h) ↔
      Separates (env.bound w) (env.bound N) (env.bound det) (env.bound g) (env.bound h) := by
  simp only [separates,Separates,NatLe,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_mem_iff,
    Project.Formula.satisfies_disj_iff,Project.Formula.satisfies_neg_iff,
    Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM),Project.Term.eval_bound,
    KuratowskiZF.code_correct hM,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge]
  rfl

def Separation (w D chain H N det : M.Carrier .set) : Prop := ∀ g h C E,
  (Project.FirstOrderSemantics.reduct M).mem g H → (Project.FirstOrderSemantics.reduct M).mem h H →
  Class w D chain H g C → Class w D chain H h E → C ≠ E → Separates w N det g h

def separation {m : Nat} (w D chain H N det : Fin m) : Project.Formula 1 m :=
  (.forallE (.forallE (.forallE (.forallE (.imp (.mem (.bound 3) (.bound H.succ.succ.succ.succ)) (.imp (.mem (.bound 2) (.bound H.succ.succ.succ.succ)) (.imp (ConstructionGermCosets.eqClass w.succ.succ.succ.succ D.succ.succ.succ.succ chain.succ.succ.succ.succ H.succ.succ.succ.succ 3 1) (.imp (ConstructionGermCosets.eqClass w.succ.succ.succ.succ D.succ.succ.succ.succ chain.succ.succ.succ.succ H.succ.succ.succ.succ 2 0) (.imp (.neg (Project.Formula.extensionalEq (.bound 1) (.bound 0))) (separates w.succ.succ.succ.succ N.succ.succ.succ.succ det.succ.succ.succ.succ 3 2))))))))))

theorem separation_freeClosed {m : Nat} (w D chain H N det : Fin m) : (separation w D chain H N det).FreeClosed := by
  simp -implicitDefEqProofs [separation,Definitional.Formula.FreeClosed,ConstructionGermCosets.eqClass_freeClosed,
    Project.Formula.extensionalEq,separates_freeClosed]

theorem separation_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w D chain H N det : Fin m) :
    Project.Formula.satisfies env (separation w D chain H N det) ↔
      Separation (env.bound w) (env.bound D) (env.bound chain) (env.bound H) (env.bound N) (env.bound det) := by
  simp only [separation,Separation,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_mem_iff,Project.Formula.satisfies_neg_iff,Project.Term.eval_bound,
    Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM),
    ConstructionGermCosets.eqClass_semantics hM,separates_semantics hM]
  rfl

def constructionSentence {m : Nat} (w D I mul unit q zero root vertices chain H Q reps N X det : Fin m) : Project.Sentence where
  formula := Project.Formula.forallClosure m (.imp (Project.Formula.isOmega (.bound w)) (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid D mul unit)) (.imp (ConstructionProbeSharedIntersections.conditionalJoins D mul) (.imp (ProjectSyntax.encode id (Source.SetLanguage.injection q D I)) (.imp (ConstructionComponentCofinal.chain w D I mul q zero root vertices chain) (.imp (ConstructionGermCosets.carrier D I mul q root H) (.imp (ConstructionGermCosets.classes w D chain H Q) (.imp (ConstructionGermDetectors.representatives H Q reps) (.imp (ConstructionGermDetectors.nonidentity w D chain Q reps N) (.imp (ConstructionGermDetectors.detectors D I chain X reps det) (.imp (Project.Formula.isCartesianProduct PureKuratowskiProject.convention (.bound X) (.bound N) (.bound w)) (separation w D chain H N det))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,Project.Formula.isOmega,
      Project.Formula.isCartesianProduct,ConstructionProbeSharedIntersections.conditionalJoins_freeClosed,
      ConstructionComponentCofinal.chain_freeClosed,ConstructionGermCosets.carrier_freeClosed,ConstructionGermCosets.classes_freeClosed,
      ConstructionGermDetectors.representatives_freeClosed,ConstructionGermDetectors.nonidentity_freeClosed,
      ConstructionGermDetectors.detectors_freeClosed,separation_freeClosed]

theorem construction_models {m : Nat} (w D I mul unit q zero root vertices chain H Q reps N X det : Fin m)
    (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (constructionSentence w D I mul unit q zero root vertices chain H Q reps N X det)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) (constructionSentence w D I mul unit q zero root vertices chain H Q reps N X det)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_isOmega_iff,
    Project.Formula.satisfies_isCartesianProduct_iff (KuratowskiZF.interpretation hM),Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),
    ForcingSupportSize.injection_semantics (M := M),ConstructionProbeSharedIntersections.conditionalJoins_semantics hM,
    ConstructionComponentCofinal.chain_semantics hM,ConstructionGermCosets.carrier_semantics hM,ConstructionGermCosets.classes_semantics hM,
    ConstructionGermDetectors.representatives_semantics hM,ConstructionGermDetectors.nonidentity_semantics hM,
    ConstructionGermDetectors.detectors_semantics hM,separation_semantics hM]
  intro hw hm hJ hq hChain hH hQ hReps hN hDet hX g h C E hg hh hC hE hne
  exact detector_separates hM hw hm hJ hq hChain hH hQ hReps hN hDet hX hg hh hC hE hne

theorem construction_kernel_certificate {m : Nat} (w D I mul unit q zero root vertices chain H Q reps N X det : Fin m) : FirstOrder.Derives nativeZF []
    (Project.fo_sentence (constructionSentence w D I mul unit q zero root vertices chain H Q reps N X det)) :=
  ModelTransfer.derives (fun _ hM => construction_models w D I mul unit q zero root vertices chain H Q reps N X det hM)

theorem relative_kernel_certificate {m : Nat} (w D I mul unit q zero root vertices chain H Q reps N X det : Fin m) : FirstOrder.Derives nativeZF []
    (Project.fo_sentence (ConstructibleGround.relative (constructionSentence w D I mul unit q zero root vertices chain H Q reps N X det))) := by
  apply ModelTransfer.derives
  intro M hM
  have hL := ConstructibleSource.model_zf hM
  apply ConstructibleGround.relative_models hM (constructionSentence w D I mul unit q zero root vertices chain H Q reps N X det)
  exact (Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hL)
    (constructionSentence w D I mul unit q zero root vertices chain H Q reps N X det)).mp (construction_models w D I mul unit q zero root vertices chain H Q reps N X det hL)

end PPAC.Migration.ConstructionGermSeparation
