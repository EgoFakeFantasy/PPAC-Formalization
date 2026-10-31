/- Pinned StableSelectors.detectorSites_countable and representative_eventually.
The actual whole quotient count bounds the full image of all chosen coset
representatives acting on all detector sequences. Consumer: good_dense. -/
import PPAC.Migration.ConstructionGermDetectors

namespace PPAC.Migration.ConstructionGermDetectorSites
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionGermDetectors (Representatives Nonidentity Detectors Laws)
open ConstructionGermCosets (Carrier Classes)
open ConstructionComponentCofinal (Chain)
open ForcingSupportSize (MapsTo Small)
open ForcingConditionGraphs (function_input function_unique)
open ConstructionFractionOrder (NatLe)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def Value (reps det p y : M.Carrier .set) : Prop := ∃ C t pi x,
  PureKuratowski.Code M p C t ∧ PureKuratowski.PairMember M C pi reps ∧
    PureKuratowski.PairMember M t x det ∧ PureKuratowski.PairMember M x y pi

def Sites (Q X reps det S : M.Carrier .set) : Prop := ∀ y,
  (Project.FirstOrderSemantics.reduct M).mem y S ↔ ∃ C t pi x,
    (Project.FirstOrderSemantics.reduct M).mem C Q ∧ (Project.FirstOrderSemantics.reduct M).mem t X ∧
    PureKuratowski.PairMember M C pi reps ∧ PureKuratowski.PairMember M t x det ∧ PureKuratowski.PairMember M x y pi

def value {m : Nat} (reps det p y : Fin m) : Project.Formula 1 m :=
  .existsE (.existsE (.existsE (.existsE
    (.conj (PureKuratowskiProject.code (.bound p.succ.succ.succ.succ) (.bound 3) (.bound 2))
    (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge reps.succ.succ.succ.succ 3 1))
    (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge det.succ.succ.succ.succ 2 0))
      (ProjectSyntax.encode id (Source.SetLanguage.edge 1 0 y.succ.succ.succ.succ))))))))

theorem value_freeClosed {m : Nat} (reps det p y : Fin m) : (value reps det p y).FreeClosed := by
  simp -implicitDefEqProofs [value,Definitional.Formula.FreeClosed,PureKuratowskiProject.code,ProjectSyntax.freeClosed]

theorem value_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (reps det p y : Fin m) :
    Project.Formula.satisfies env (value reps det p y) ↔ Value (env.bound reps) (env.bound det) (env.bound p) (env.bound y) := by
  simp only [value,Value,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    KuratowskiZF.code_correct hM,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge]
  rfl

def sites {m : Nat} (Q X reps det S : Fin m) : Project.Formula 1 m :=
  .forallE (.iff (.mem (.bound 0) (.bound S.succ)) (.existsE (.existsE (.existsE (.existsE
    (.conj (.mem (.bound 3) (.bound Q.succ.succ.succ.succ.succ))
    (.conj (.mem (.bound 2) (.bound X.succ.succ.succ.succ.succ))
    (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge reps.succ.succ.succ.succ.succ 3 1))
    (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge det.succ.succ.succ.succ.succ 2 0))
      (ProjectSyntax.encode id (Source.SetLanguage.edge 1 0 4)))))))))))

theorem sites_freeClosed {m : Nat} (Q X reps det S : Fin m) : (sites Q X reps det S).FreeClosed := by
  simp -implicitDefEqProofs [sites,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed]

theorem sites_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (Q X reps det S : Fin m) :
    Project.Formula.satisfies env (sites Q X reps det S) ↔ Sites (env.bound Q) (env.bound X) (env.bound reps) (env.bound det) (env.bound S) := by
  simp only [sites,Sites,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_iff_iff,
    Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge]
  rfl

theorem value_unique {D I mul q root H Q X reps det p y z : M.Carrier .set}
    (hH : Carrier D I mul q root H) (hReps : Representatives H Q reps) (hDet : MapsTo X I det)
    (hy : Value reps det p y) (hz : Value reps det p z) : y = z := by
  obtain ⟨C,t,pi,x,hp,hpi,ht,hxy⟩ := hy
  obtain ⟨C',t',pi',x',hp',hpi',ht',hxz⟩ := hz
  obtain ⟨rfl,rfl⟩ := PureKuratowski.code_injective hp hp'
  have he := function_unique hReps.1.1 hpi hpi'
  subst pi'
  have he := function_unique hDet.1 ht ht'
  subst x'
  exact function_unique ((hH pi).mp (hReps.1.2 C pi hpi)).1.1.1 hxy hxz

theorem exists_sites (hM : FirstOrder.Theory.Models M nativeZF)
    {w D I mul q root chain H Q N X reps det : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hH : Carrier D I mul q root H) (hReps : Representatives H Q reps)
    (hN : Nonidentity w D chain Q reps N)
    (hX : (Project.FirstOrderSemantics.reduct M).IsCartesianProduct (KuratowskiZF.interpretation hM) X N w)
    (hDet : Detectors D I chain X reps det) (hQSmall : Small Q w) :
    ∃ S, Sites Q X reps det S ∧ Small S w ∧ (Project.FirstOrderSemantics.reduct M).MemberSubset S I := by
  have hZF := ModelTransfer.project_models_iff.mp hM
  let P := KuratowskiZF.interpretation hM
  obtain ⟨id,hId⟩ := ZF.exists_identityBijection hZF P w
  have hInf : (Project.FirstOrderSemantics.reduct M).IsInfiniteCardinal P w w :=
    ⟨ExistingCardinalBounds.omega_cardinal_l P hZF hw,id,hId.1⟩
  have hNSmall := ForcingSupportSize.small_subset hM (fun C hC => ((hN C).mp hC).1) hQSmall
  have hXS := ExistingCardinalBounds.infinite_product_l P hZF hw hInf
    ((ForcingSupportSize.native_small hM N w).mp hNSmall) ⟨id,hId.1⟩ hX
  obtain ⟨W,hW⟩ := ZF.exists_cartesianProduct hZF P Q X
  have hWS := ExistingCardinalBounds.infinite_product_l P hZF hw hInf
    ((ForcingSupportSize.native_small hM Q w).mp hQSmall) hXS hW
  let schema : Project.BinarySchema 2 := { body := value 2 3 1 0, freeClosed := value_freeClosed .. }
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 2 := {
    bound := Fin.cases reps (fun _ => det), free := fun _ => I }
  have he p y : schema.denote env p y ↔ Value reps det p y := value_semantics hM ((env.push p).push y) 2 3 1 0
  have ht : ∀ p, (Project.FirstOrderSemantics.reduct M).mem p W → ∃ y, schema.denote env p y := by
    intro p hp
    obtain ⟨C,hC,t,ht,hp⟩ := (hW p).mp hp
    obtain ⟨pi,hpi,_⟩ := hReps.1.1.2 C hC
    obtain ⟨x,hx,_⟩ := hDet.1.1.2 t ht
    obtain ⟨y,hy,_⟩ := ((hH pi).mp (hReps.1.2 C pi hpi)).1.1.1.2 x (hDet.1.2 t x hx)
    exact ⟨y,(he p y).mpr ⟨C,t,pi,x,hp,hpi,hx,hy⟩⟩
  have hu : ∀ p, (Project.FirstOrderSemantics.reduct M).mem p W → ∀ y z,
      schema.denote env p y → schema.denote env p z → y = z :=
    fun p _ y z hy hz => value_unique hH hReps hDet.1 ((he p y).mp hy) ((he p z).mp hz)
  obtain ⟨S,hS⟩ := ZF.exists_functionalImageOn hZF schema env W ht hu
  obtain ⟨graph,hGraph,hEdge⟩ := ZF.exists_setFunctionFromTo_of_denote hZF P schema env ht hu
    (fun p y hp hy => (hS y).mpr ⟨p,hp,hy⟩)
  have hSmall := ExistingOrdinalImage.ordinal_image_bound_l P hZF hInf.1.1 hWS hGraph (by
    intro y hy
    obtain ⟨p,hp,hy⟩ := (hS y).mp hy
    exact ⟨p,hp,(hEdge p y).mpr ⟨hp,hy⟩⟩)
  have hSites : Sites Q X reps det S := by
    intro y
    constructor
    · intro hy
      obtain ⟨p,hp,hy⟩ := (hS y).mp hy
      obtain ⟨C,hC,t,ht,hp⟩ := (hW p).mp hp
      obtain ⟨C',t',pi,x,hp',hpi,hx,hxy⟩ := (he p y).mp hy
      obtain ⟨rfl,rfl⟩ := PureKuratowski.code_injective hp hp'
      exact ⟨C,t,pi,x,hC,ht,hpi,hx,hxy⟩
    · rintro ⟨C,t,pi,x,hC,ht,hpi,hx,hxy⟩
      obtain ⟨p,hp⟩ := KuratowskiZF.exists_code hM C t
      exact (hS y).mpr ⟨p,(hW p).mpr ⟨C,hC,t,ht,hp⟩,(he p y).mpr ⟨C,t,pi,x,hp,hpi,hx,hxy⟩⟩
  refine ⟨S,hSites,(ForcingSupportSize.native_small hM S w).mpr hSmall,?_⟩
  intro y hy
  obtain ⟨C,t,pi,x,_,_,hpi,_,hxy⟩ := (hSites y).mp hy
  exact ((hH pi).mp (hReps.1.2 C pi hpi)).1.1.2 x y hxy

def Covers (w H det S : M.Carrier .set) : Prop := ∀ g,
  (Project.FirstOrderSemantics.reduct M).mem g H → ∃ N, (Project.FirstOrderSemantics.reduct M).mem N w ∧
    ∀ C n p x y, PureKuratowski.Code M p C n → PureKuratowski.PairMember M p x det → NatLe N n →
      PureKuratowski.PairMember M x y g → (Project.FirstOrderSemantics.reduct M).mem y S

/-- The one countable site set covers every actual group element on every
detector eventually. This is the source representative_eventually step in
complete_of_covered, not an enumeration of the possibly uncountable group. -/
theorem covers (hM : FirstOrder.Theory.Models M nativeZF)
    {w D I chain H Q X reps det S : M.Carrier .set}
    (hQ : Classes w D chain H Q) (hReps : Representatives H Q reps)
    (hDet : Detectors D I chain X reps det) (hSites : Sites Q X reps det S)
    (hLaws : Laws w D chain det) : Covers w H det S := by
  intro g hg
  obtain ⟨C,hClass⟩ := ConstructionGermCosets.exists_class hM w D chain H g
  have hCQ := (hQ C).mpr ⟨g,hg,hClass⟩
  obtain ⟨rep,hrep,_⟩ := hReps.1.1.2 C hCQ
  have hSame := ((hClass rep).mp (hReps.2 C rep hrep)).2
  obtain ⟨N,hN,hAgree⟩ := hLaws.2 g rep hSame
  refine ⟨N,hN,?_⟩
  intro delta n p x y hp hx hNn hxy
  exact (hSites y).mpr ⟨C,p,rep,x,hCQ,function_input hDet.1.1 hx,hrep,hx,
    (hAgree delta n p x y hp hx hNn).mp hxy⟩

def coversFormula {m : Nat} (w H det S : Fin m) : Project.Formula 1 m :=
  (.forallE (.imp (.mem (.bound 0) (.bound H.succ)) (.existsE (.conj (.mem (.bound 0) (.bound w.succ.succ)) (.forallE (.forallE (.forallE (.forallE (.forallE (.imp (PureKuratowskiProject.code (.bound 2) (.bound 4) (.bound 3)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge det.succ.succ.succ.succ.succ.succ.succ 2 1)) (.imp (.disj (Project.Formula.extensionalEq (.bound 5) (.bound 3)) (.mem (.bound 5) (.bound 3))) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge 6 1 0)) (.mem (.bound 0) (.bound S.succ.succ.succ.succ.succ.succ.succ)))))))))))))))

theorem coversFormula_freeClosed {m : Nat} (w H det S : Fin m) : (coversFormula w H det S).FreeClosed := by
  simp -implicitDefEqProofs [coversFormula,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,PureKuratowskiProject.code,Project.Formula.extensionalEq]

theorem coversFormula_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w H det S : Fin m) :
    Project.Formula.satisfies env (coversFormula w H det S) ↔ Covers (env.bound w) (env.bound H) (env.bound det) (env.bound S) := by
  simp only [coversFormula,Covers,NatLe,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    Project.Formula.satisfies_disj_iff,Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM),
    KuratowskiZF.code_correct hM,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge]
  rfl

theorem construction (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M))
    {w D I mul q zero root vertices chain H Q : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hC : Chain w D I mul q zero root vertices chain)
    (hH : Carrier D I mul q root H) (hQ : Classes w D chain H Q) (hSmall : Small Q w) :
    ∃ reps N X det S, Representatives H Q reps ∧ Nonidentity w D chain Q reps N ∧
      (Project.FirstOrderSemantics.reduct M).IsCartesianProduct (KuratowskiZF.interpretation hM) X N w ∧
      Detectors D I chain X reps det ∧ Laws w D chain det ∧ Sites Q X reps det S ∧ Small S w ∧
      (Project.FirstOrderSemantics.reduct M).MemberSubset S I ∧ Covers w H det S := by
  obtain ⟨reps,N,X,det,hReps,hN,hX,hDet,hLaws⟩ := ConstructionGermDetectors.construction hM hChoice hzw hC hH hQ
  obtain ⟨S,hSites,hCount,hSub⟩ := exists_sites hM hw hH hReps hN hX hDet hSmall
  exact ⟨reps,N,X,det,S,hReps,hN,hX,hDet,hLaws,hSites,hCount,hSub,covers hM hQ hReps hDet hSites hLaws⟩

def constructionSentence {m : Nat} (w D I mul q zero root vertices chain H Q : Fin m) : Project.Sentence where
  formula := Project.Formula.forallClosure m (.imp (Project.Formula.isOmega (.bound w)) (.imp (.mem (.bound zero) (.bound w)) (.imp (ConstructionComponentCofinal.chain w D I mul q zero root vertices chain) (.imp (ConstructionGermCosets.carrier D I mul q root H) (.imp (ConstructionGermCosets.classes w D chain H Q) (.imp (ProjectSyntax.encode id (ForcingSupportSize.small Q w)) (.existsE (.existsE (.existsE (.existsE (.existsE (.conj (ConstructionGermDetectors.representatives H.succ.succ.succ.succ.succ Q.succ.succ.succ.succ.succ 4) (.conj (ConstructionGermDetectors.nonidentity w.succ.succ.succ.succ.succ D.succ.succ.succ.succ.succ chain.succ.succ.succ.succ.succ Q.succ.succ.succ.succ.succ 4 3) (.conj (Project.Formula.isCartesianProduct PureKuratowskiProject.convention (.bound 2) (.bound 3) (.bound w.succ.succ.succ.succ.succ)) (.conj (ConstructionGermDetectors.detectors D.succ.succ.succ.succ.succ I.succ.succ.succ.succ.succ chain.succ.succ.succ.succ.succ 2 4 1) (.conj (ConstructionGermDetectors.laws w.succ.succ.succ.succ.succ D.succ.succ.succ.succ.succ chain.succ.succ.succ.succ.succ 1) (.conj (sites Q.succ.succ.succ.succ.succ 2 4 1 0) (.conj (ProjectSyntax.encode id (ForcingSupportSize.small 0 w.succ.succ.succ.succ.succ)) (.conj (Project.Formula.subset (.bound 0) (.bound I.succ.succ.succ.succ.succ)) (coversFormula w.succ.succ.succ.succ.succ H.succ.succ.succ.succ.succ 1 0))))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,Project.Formula.isOmega,Project.Formula.isCartesianProduct,ProjectSyntax.freeClosed,
      ConstructionComponentCofinal.chain_freeClosed,ConstructionGermCosets.carrier_freeClosed,ConstructionGermCosets.classes_freeClosed,
      ConstructionGermDetectors.representatives_freeClosed,ConstructionGermDetectors.nonidentity_freeClosed,ConstructionGermDetectors.detectors_freeClosed,
      ConstructionGermDetectors.laws_freeClosed,sites_freeClosed,coversFormula_freeClosed]

theorem construction_models {m : Nat} (w D I mul q zero root vertices chain H Q : Fin m)
    (hM : FirstOrder.Theory.Models M nativeZF) (hChoice : ConstructionDirectedCardinality.Choice (M := M)) :
    (Project.fo_sentence (constructionSentence w D I mul q zero root vertices chain H Q)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) (constructionSentence w D I mul q zero root vertices chain H Q)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,Project.Formula.satisfies_isOmega_iff,Project.Formula.satisfies_subset_iff,
    Project.Formula.satisfies_isCartesianProduct_iff (KuratowskiZF.interpretation hM),
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ForcingSupportSize.small_semantics (M := M),
    ConstructionComponentCofinal.chain_semantics hM,ConstructionGermCosets.carrier_semantics hM,ConstructionGermCosets.classes_semantics hM,
    ConstructionGermDetectors.representatives_semantics hM,ConstructionGermDetectors.nonidentity_semantics hM,
    ConstructionGermDetectors.detectors_semantics hM,ConstructionGermDetectors.laws_semantics hM,sites_semantics hM,coversFormula_semantics hM]
  exact construction hM hChoice

theorem construction_kernel_certificate {m : Nat} (w D I mul q zero root vertices chain H Q : Fin m) : FirstOrder.Derives nativeZF []
    (Project.fo_sentence (ConstructibleGround.relative (constructionSentence w D I mul q zero root vertices chain H Q))) := by
  apply ModelTransfer.derives
  intro M hM
  have hL := ConstructibleSource.model_zf hM
  have hRawChoice := (Project.FirstOrderSemantics.sentence_correct
    (ModelTransfer.extensionality hL) Axioms.choice).mp (ConstructibleSource.model_choice hM)
  let z := Classical.choice ((ConstructibleSource.model hM).nonempty .set)
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct (ConstructibleSource.model hM)) 0 :=
    { bound := Fin.elim0, free := fun _ => z }
  have hSat : Project.Formula.satisfies env (ConstructionDirectedCardinality.choice (m := 0)) := by
    change Project.Formula.satisfies env (Axioms.choice.formula.rename Fin.elim0)
    rw [Project.Formula.satisfies_rename]
    exact hRawChoice env.free
  have hChoice := (ConstructionDirectedCardinality.choice_semantics hL env).mp hSat
  apply ConstructibleGround.relative_models hM (constructionSentence w D I mul q zero root vertices chain H Q)
  exact (Project.FirstOrderSemantics.sentence_correct
    (ModelTransfer.extensionality hL) (constructionSentence w D I mul q zero root vertices chain H Q)).mp (construction_models w D I mul q zero root vertices chain H Q hL hChoice)

end PPAC.Migration.ConstructionGermDetectorSites
