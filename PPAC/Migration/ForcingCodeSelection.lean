/- Pinned CodeLinks.IsSelected:78 and its monotonicity/covariance consumers.
The internal code carrier itself is the small index set; the prescribed code
order is unchanged. Reuse ProjectDecode rather than a second formula compiler. -/
import PPAC.Migration.ForcingTailGroup
import PPAC.Migration.ForcingWorksCovariance
import PPAC.Migration.ProjectDecode

namespace PPAC.Migration.ForcingCodeSelection
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ForcingProductSymmetry (orderFormula)
open ForcingMapConditions (MapRel)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 6000000
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

private theorem decode_term {d n : Nat} (r : Fin d → Fin n) (t : Project.Term d)
    (h : t.freeSupport = []) (env : Fin n → M.Carrier .set) (free : FreeVarId → M.Carrier .set) :
    env (ProjectDecode.term r t h) = Definitional.Term.eval ({bound := fun i => env (r i), free := free} : SetTheory.Env (Project.FirstOrderSemantics.reduct M) d) t := by
  cases t with
  | bound i => rfl
  | free x => cases h

/-- Consumer bridge for the EXISTING decoder, with arbitrary bound assignments. -/
private theorem decode_realizes (hM : FirstOrder.Theory.Models M nativeZF) {d n : Nat}
    (r : Fin d → Fin n) (p : Project.Formula 1 d) (h : p.FreeClosed)
    (env : Fin n → M.Carrier .set) (free : FreeVarId → M.Carrier .set) :
    Source.Formula.Realize (Project.FirstOrderSemantics.reduct M).mem env (ProjectDecode.formula r p h) ↔
      Project.Formula.satisfies ({bound := fun i => env (r i), free := free} : SetTheory.Env (Project.FirstOrderSemantics.reduct M) d) p := by
  induction p generalizing n with
  | falsum | truth => simp [ProjectDecode.formula,Source.Formula.Realize,
      Project.Formula.satisfies,Definitional.Semantics.satisfies]
  | mem x y =>
    simp only [Definitional.Formula.FreeClosed] at h
    simp only [ProjectDecode.formula,Source.Formula.Realize,Project.Formula.satisfies_mem_iff,
      decode_term r x h.1 env free,decode_term r y h.2 env free]
  | atom s hs args =>
    simp only [Definitional.Formula.FreeClosed] at h
    cases s with
    | extensionalEq =>
      simp only [ProjectDecode.formula,Source.Formula.Realize,
        decode_term r (args 0) (h 0) env free,decode_term r (args 1) (h 1) env free,
        Project.Formula.satisfies,Definitional.Semantics.satisfies,Project.Semantics.interpretation]
      change (_ = _) ↔ ∀ value, (Project.FirstOrderSemantics.reduct M).mem value _ ↔
        (Project.FirstOrderSemantics.reduct M).mem value _
      constructor
      · intro he
        change ∀ value, (Project.FirstOrderSemantics.reduct M).mem value
          (Definitional.Term.eval {bound := fun i => env (r i),free := free} (args 0)) ↔
          (Project.FirstOrderSemantics.reduct M).mem value
          (Definitional.Term.eval {bound := fun i => env (r i),free := free} (args 1))
        exact he ▸ (fun _ => Iff.rfl)
      · exact (ModelTransfer.extensionality hM).eq_of_same_members _ _
    | subset =>
      simp only [ProjectDecode.formula,ProjectDecode.subset,Source.Formula.Realize,
        Fin.lastCases_last,Fin.lastCases_castSucc,
        decode_term r (args 0) (h 0) env free,decode_term r (args 1) (h 1) env free,
        Project.Formula.satisfies,Definitional.Semantics.satisfies,Project.Semantics.interpretation]
      rfl
  | neg p ih =>
    simp only [Definitional.Formula.FreeClosed] at h
    simpa only [ProjectDecode.formula,Source.Formula.neg,Source.Formula.Realize,
      Project.Formula.satisfies_neg_iff] using not_congr (ih r h env)
  | conj p q ihp ihq | disj p q ihp ihq | imp p q ihp ihq | iff p q ihp ihq =>
    simp only [Definitional.Formula.FreeClosed] at h
    simp only [ProjectDecode.formula,Source.Formula.iff,Source.Formula.Realize,
      Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_disj_iff,
      Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_iff_iff,ihp r h.1 env,ihq r h.2 env]
    try exact ⟨fun h => ⟨h.1,h.2⟩,fun h => ⟨h.mp,h.mpr⟩⟩
  | forallE p ih | existsE p ih =>
    simp only [Definitional.Formula.FreeClosed] at h
    simp only [ProjectDecode.formula,Source.Formula.Realize,Project.Formula.satisfies_forall_iff,
      Project.Formula.satisfies_exists_iff]
    have he (x : M.Carrier .set) :
        ({bound := fun i => Fin.lastCases x env (ProjectDecode.lift r i), free := free} : SetTheory.Env (Project.FirstOrderSemantics.reduct M) _) =
          ({bound := fun i => env (r i),free := free} : SetTheory.Env (Project.FirstOrderSemantics.reduct M) _).push x := by
      apply congrArg (fun b => (⟨b,free⟩ : SetTheory.Env (Project.FirstOrderSemantics.reduct M) _))
      funext i
      refine Fin.cases ?_ (fun j => ?_) i <;> simp only [ProjectDecode.lift,Fin.cases_zero,Fin.cases_succ,Fin.lastCases_last,Fin.lastCases_castSucc]
    first
    | exact forall_congr' (fun x => (ih (ProjectDecode.lift r) h (Fin.lastCases x env)).trans (Iff.of_eq (congrArg (fun e => Project.Formula.satisfies e p) (he x))))
    | exact exists_congr (fun x => (ih (ProjectDecode.lift r) h (Fin.lastCases x env)).trans (Iff.of_eq (congrArg (fun e => Project.Formula.satisfies e p) (he x))))

def IsSelected {k : Nat} (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k)
    (I G F mul q bound labels E root w chain codes order : Fin k) (a d : M.Carrier .set) : Prop :=
  ForcingPersistentSelection.Selected (fun p q => ForcingPowerName.Subset q p)
    (ForcingPersistentWorks.Works (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) env
      (fun j => env (rho j)) (env I) (env G) (env F) (env mul) (env q) (env bound) (env labels)
      (env E) (env root) (env w) (env chain))
    (ForcingPersistentCodes.Same (orderFormula (rho 0) mul) env (env (rho 6)) (env w) (env chain))
    (env (rho 3)) (env codes) (env order) a d

def selected {k m : Nat} (rho : Fin 7 → Fin k)
    (I G F mul q bound labels E root w chain codes order : Fin k)
    (base : Fin k → Fin m) (a d : Fin m) : Project.Formula 1 m :=
  ForcingPersistentSelection.selected ForcingPersistentWorks.lower
    (ForcingPersistentWorks.working rho I G F mul q bound labels E root w chain)
    (ForcingPersistentWorks.equalAt rho mul w chain) base (base (rho 3)) (base codes) (base order) a d

theorem selected_freeClosed {k m : Nat} (rho : Fin 7 → Fin k)
    (I G F mul q bound labels E root w chain codes order : Fin k)
    (base : Fin k → Fin m) (a d : Fin m) :
    (selected rho I G F mul q bound labels E root w chain codes order base a d).FreeClosed := by
  simp [selected,ForcingPersistentSelection.selected,ForcingPersistentSelection.rel2,
    ForcingPersistentSelection.rel3,ForcingPersistentWorks.lower,Definitional.Formula.FreeClosed,
    ProjectSyntax.freeClosed,ForcingPersistentWorks.working_freeClosed,ForcingPersistentWorks.equalAt_freeClosed]

theorem selected_semantics (hM : FirstOrder.Theory.Models M nativeZF) {k m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (rho : Fin 7 → Fin k)
    (I G F mul q bound labels E root w chain codes order : Fin k)
    (base : Fin k → Fin m) (a d : Fin m) :
    Project.Formula.satisfies env (selected rho I G F mul q bound labels E root w chain codes order base a d) ↔
      IsSelected (fun j => env.bound (base j)) rho I G F mul q bound labels E root w chain codes order
        (env.bound a) (env.bound d) := by
  simp only [selected,ForcingPersistentSelection.selected_semantics hM,ForcingPersistentSelection.Selected,
    ForcingPersistentWorks.lower_semantics,ForcingPersistentWorks.working_semantics hM,
    ForcingPersistentWorks.equalAt_semantics hM,IsSelected]
  rfl

/-- Source parameters come first, then the actual code and Cohen condition. -/
def relation {k : Nat} (rho : Fin 7 → Fin k)
    (I G F mul q bound labels E root w chain codes order : Fin k) : Source.Formula (k+2) :=
  ProjectDecode.formula id
    (selected rho I G F mul q bound labels E root w chain codes order
      (fun j => j.castSucc.castSucc) (Fin.last k).castSucc (Fin.last (k+1)))
    (selected_freeClosed rho I G F mul q bound labels E root w chain codes order _ _ _)

theorem mapRel_relation (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k)
    (I G F mul q bound labels E root w chain codes order : Fin k) (a d : M.Carrier .set) :
    MapRel (relation rho I G F mul q bound labels E root w chain codes order) env a d ↔
      IsSelected env rho I G F mul q bound labels E root w chain codes order a d := by
  unfold MapRel relation
  rw [decode_realizes hM _ _ _ _ (fun _ => d),selected_semantics hM]
  simp only [Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]

/-- No code-order rearrangement or standardness assumption is involved. -/
theorem isSelected_mono {k : Nat} {env : Fin k → M.Carrier .set} {rho : Fin 7 → Fin k}
    {I G F mul q bound labels E root w chain codes order : Fin k} {a d e : M.Carrier .set}
    (hde : ForcingPowerName.Subset d e)
    (ha : IsSelected env rho I G F mul q bound labels E root w chain codes order a d) :
    IsSelected env rho I G F mul q bound labels E root w chain codes order a e :=
  ⟨ForcingPersistentWorks.works_mono hde ha.1,fun f hf hef => ha.2 f hf (fun z hz => hef z (hde z hz))⟩

theorem monotone (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k)
    (I G F mul q bound labels E root w chain codes order : Fin k) :
    ForcingCohenRankConsumers.Monotone (relation rho I G F mul q bound labels E root w chain codes order)
      env (env (rho 2)) (env w) (env codes) := by
  intro a d e _ _ _ hde ha
  exact (mapRel_relation hM env rho I G F mul q bound labels E root w chain codes order a e).mpr
    (isSelected_mono hde ((mapRel_relation hM env rho I G F mul q bound labels E root w chain codes order a d).mp ha))

theorem isSelected_covariance (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k)
    (I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound pi inv c act ai zero root vertices chain names codes order group : Fin k) (code : M.Carrier .set)
    (hm : ForcingDiagramPoset.LeftCancelMonoid (env (rho 0)) (env mul) (env one))
    (hJ : ConstructionProbeSharedIntersections.ConditionalJoins (env (rho 0)) (env mul))
    (hData : ForcingProductCovariance.SystemData (fun j => env (rho j)) (env I) (env K) (env B) (env w) (env G) (env F) (env mu) (env pi) (env inv) (env c) (env act) (env ai))
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega (env w))
    (hMu : (Project.FirstOrderSemantics.reduct M).IsInfiniteCardinal (KuratowskiZF.interpretation hM) (env w) (env mu))
    (hI : (Project.FirstOrderSemantics.reduct M).IsHartogsNumber (KuratowskiZF.interpretation hM) (env I) (env mu))
    (hSmallD : ForcingSupportSize.Small (env (rho 0)) (env mu))
    (hSmall : ForcingSupportSize.Small (env w) (env mu))
    (hMergers : ConstructionSaturationMergers.AllMergers (env w) (env history) (env kappa))
    (hRow : ConstructionTowerHistory.Row (env history) (env kappa) (env (rho 0)) (env mul) (env one) (env mark) (env H) (env C) (env incoming) (env base) (env kappa))
    (hLabelMap : ForcingConditionGraphs.FunctionOn (env K) (env labelMap))
    (hTop : ForcingWithTopCarrier.Empty (env top))
    (hLabels : ForcingLabelSet.LabelSet (env (rho 6)) (env I) (env K) (env labelMap) (env top) (env bit) (env labels))
    (hLabelBound : ForcingLabelBound.LabelBound (env (rho 6)) (env I) (env K) (env labelMap) (env top) (env bit) (env bound))
    (hBound : ForcingSupportedNames.Supported (fun j => env (rho j)) (env G) (env bound))
    (hq : ForcingSupportSize.Injection (env (rho 0)) (env I) (env q))
    (hA : ForcingSupportedNames.Range (env (rho 0)) (env q) (env A))
    (hHq : ForcingLabelPermutations.Fixing (env G) (env A) (env Hq))
    (hE : ForcingSupportedNames.Supported (fun j => env (rho j)) (env Hq) (env E))
    (hChain : ConstructionComponentCofinal.Chain (env w) (env (rho 0)) (env I) (env mul) (env q) (env zero) (env root) (env vertices) (env chain))
    (hCarrier : ForcingTailCodes.Carrier (fun j => env (rho j)) (env G) (env F) (env bound) (env w) (env names) (env chain) (env codes))
    (hCodeMem : (Project.FirstOrderSemantics.reduct M).mem code (env codes))
    (hGroup : ForcingTailGroup.TailGroup (env w) (env (rho 0)) (env G) (env chain) (env group))
    (hpiGroup : (Project.FirstOrderSemantics.reduct M).mem (env pi) (env group))
    {ac d dT : M.Carrier .set}
    (hc : ForcingLocalTransport.CohenPart (env (rho 1)) (env (rho 2)) (env (rho 3)) (env pi) ac)
    (hdd : PureKuratowski.PairMember M d dT ac) :
    IsSelected env rho I G F mul q bound labels E root w chain codes order code dT ↔
      IsSelected env rho I G F mul q bound labels E root w chain codes order code d := by
  obtain ⟨hpiG,hFix,⟨rootT,hRoot,hStab⟩,hTail⟩ :=
    (ForcingTailGroup.tailGroup_mem hM hm hJ hq hA hData.2.1 hChain hGroup).mp hpiGroup
  have hpiHq : (Project.FirstOrderSemantics.reduct M).mem (env pi) (env Hq) := by
    apply (hHq (env pi)).mpr
    refine ⟨hpiG,?_⟩
    intro x hx
    obtain ⟨i,_,hix⟩ := (hA x).mp hx
    obtain ⟨_,y,hiy,hyx⟩ := (hFix i x).mp hix
    have he := ForcingConditionGraphs.function_unique hq.1.1 hiy hix
    exact he ▸ hyx
  exact ForcingWorksCovariance.selected_covariance_at hM hChoice env rho
    I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound
    pi inv c act ai zero root vertices chain names codes order rootT code
    hm hJ hData hw hMu hI hSmallD hSmall hMergers hRow hLabelMap hTop hLabels hLabelBound hBound
    hq hA hHq hpiHq hE hFix hRoot hStab hChain hCarrier hCodeMem hTail hc hdd

def constructionSentence {k : Nat} (rho : Fin 7 → Fin k) (I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound pi inv c act ai zero root vertices chain names code codes order group : Fin k) : Project.Sentence where
  formula :=
    let R := relation rho I G F mul q bound labels E root w chain codes order
    let up : Fin k → Fin (k+3) := fun j => j.succ.succ.succ
    Project.Formula.forallClosure k (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid (rho 0) mul one))
    (.imp (ConstructionProbeSharedIntersections.conditionalJoins (rho 0) mul)
    (.imp (ProjectSyntax.encode id (ForcingProductCovariance.systemData rho I K B w G F mu pi inv c act ai))
    (.imp (Project.Formula.isOmega (.bound w))
    (.imp (Project.Formula.isInfiniteCardinal PureKuratowskiProject.convention (.bound w) (.bound mu))
    (.imp (ConstructionSaturationIndex.hartogs mu I)
    (.imp (ProjectSyntax.encode id (ForcingSupportSize.small (rho 0) mu))
    (.imp (ProjectSyntax.encode id (ForcingSupportSize.small w mu))
    (.imp (ConstructionSaturationMergers.allMergers w history kappa)
    (.imp (ConstructionTowerHistory.row history kappa (rho 0) mul one mark H C incoming base kappa)
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.functionOn labelMap K))
    (.imp (ProjectSyntax.encode id (ForcingWithTopCarrier.empty top))
    (.imp (ProjectSyntax.encode id (ForcingLabelSet.labelSet (rho 6) I K labelMap top bit labels))
    (.imp (ProjectSyntax.encode id (ForcingLabelBound.labelBound (rho 6) I K labelMap top bit bound))
    (.imp (ProjectSyntax.encode id (ForcingEquivariantMix.fixedAll rho G bound))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.injection q (rho 0) I))
    (.imp (ProjectSyntax.encode id (ForcingSupportedNames.range (rho 0) q A))
    (.imp (ProjectSyntax.encode id (ForcingLabelPermutations.fixing G A Hq))
    (.imp (ProjectSyntax.encode id (ForcingEquivariantMix.fixedAll rho Hq E))
    (.imp (ConstructionComponentCofinal.chain w (rho 0) I mul q zero root vertices chain)
    (.imp (ForcingTailCodes.carrier rho G F bound w names chain codes)
    (.imp (.mem (.bound code) (.bound codes))
    (.imp (ForcingTailGroup.tailGroup w (rho 0) G chain group)
    (.imp (.mem (.bound pi) (.bound group))
    (.existsE (.conj
      (ProjectSyntax.encode id (ForcingLocalTransport.cohenPart (rho 1).succ (rho 2).succ (rho 3).succ pi.succ 0))
      (.forallE (.forallE (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge 2 1 0))
        (.iff (ProjectSyntax.encode id (ReplacementPredicates.rel R up (up code) 0))
          (ProjectSyntax.encode id (ReplacementPredicates.rel R up (up code) 1))))))))))))))))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
      ConstructionProbeSharedIntersections.conditionalJoins_freeClosed,
      ConstructionSaturationIndex.hartogs_freeClosed,ConstructionSaturationMergers.allMergers_freeClosed,
      ConstructionTowerHistory.row_freeClosed,ConstructionComponentCofinal.chain_freeClosed,
      ForcingTailCodes.carrier_freeClosed,ForcingTailGroup.tailGroup_freeClosed]

theorem construction_models {k : Nat} (rho : Fin 7 → Fin k) (I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound pi inv c act ai zero root vertices chain names code codes order group : Fin k)
    (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) :
    (Project.fo_sentence (constructionSentence rho I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound pi inv c act ai zero root vertices chain names code codes order group)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM),SetTheory.Structure.satisfiesSentence_iff]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro env
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_iff_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,Project.Formula.satisfies_isOmega_iff,
    Project.Formula.satisfies_isInfiniteCardinal_iff (KuratowskiZF.interpretation hM) (ModelTransfer.extensionality hM),
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),ConstructionProbeSharedIntersections.conditionalJoins_semantics hM,
    ForcingProductCovariance.systemData_semantics (M := M),ConstructionSaturationIndex.hartogs_semantics hM,
    ForcingSupportSize.small_semantics (M := M),ConstructionSaturationMergers.allMergers_semantics hM,
    ConstructionTowerHistory.row_semantics hM,ForcingConditionGraphs.functionOn_semantics (M := M),
    ForcingWithTopCarrier.empty_semantics (M := M),ForcingLabelSet.labelSet_semantics (M := M),
    ForcingLabelBound.labelBound_semantics (M := M),ForcingSupportedNames.supported_semantics (M := M),
    ForcingSupportSize.injection_semantics (M := M),ForcingSupportedNames.range_semantics (M := M),
    ForcingLabelPermutations.fixing_semantics (M := M),
    
    ConstructionComponentCofinal.chain_semantics hM,ForcingTailCodes.carrier_semantics hM,
    ForcingTailGroup.tailGroup_semantics hM,ForcingLocalTransport.cohenPart_semantics (M := M),
    KuratowskiZF.source_edge,ForcingMapConditions.rel_semantics (M := M)]
  intro hm hJ hData hw hMu hI hSmallD hSmall hMergers hRow hLabelMap hTop hLabels hLabelBound hBound hq hA hHq hE hChain hCarrier hCodeMem hGroup hpiGroup
  have hDataCopy := hData
  obtain ⟨_,_,_,_,_,_,_,hAct,_,_⟩ := hDataCopy
  obtain ⟨ac,hc⟩ := ForcingLocalTransport.part_of_action hAct
  refine ⟨ac,hc,?_⟩
  intro d dT hdd
  exact (mapRel_relation hM env rho I G F mul q bound labels E root w chain codes order (env code) dT).trans
    ((isSelected_covariance hM hChoice env rho I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound pi inv c act ai zero root vertices chain names codes order group (env code)
      hm hJ hData hw hMu hI hSmallD hSmall hMergers hRow hLabelMap hTop hLabels hLabelBound hBound hq hA hHq hE hChain hCarrier hCodeMem hGroup hpiGroup hc hdd).trans
      (mapRel_relation hM env rho I G F mul q bound labels E root w chain codes order (env code) d).symm)

theorem construction_kernel_certificate {k : Nat} (rho : Fin 7 → Fin k) (I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound pi inv c act ai zero root vertices chain names code codes order group : Fin k) :
    FirstOrder.Derives nativeZF []
      (Project.fo_sentence (ConstructibleGround.relative (constructionSentence rho I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound pi inv c act ai zero root vertices chain names code codes order group))) := by
  apply ModelTransfer.derives
  intro M hM
  have hL := ConstructibleSource.model_zf hM
  have hRawChoice := (Project.FirstOrderSemantics.sentence_correct
    (ModelTransfer.extensionality hL) Axioms.choice).mp (ConstructibleSource.model_choice hM)
  let witness := Classical.choice ((ConstructibleSource.model hM).nonempty .set)
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct (ConstructibleSource.model hM)) 0 :=
    { bound := Fin.elim0, free := fun _ => witness }
  have hSat : Project.Formula.satisfies env (ConstructionDirectedCardinality.choice (m := 0)) := by
    change Project.Formula.satisfies env (Axioms.choice.formula.rename Fin.elim0)
    rw [Project.Formula.satisfies_rename]
    exact hRawChoice env.free
  have hChoice := (ConstructionDirectedCardinality.choice_semantics hL env).mp hSat
  apply ConstructibleGround.relative_models hM (constructionSentence rho I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound pi inv c act ai zero root vertices chain names code codes order group)
  exact (Project.FirstOrderSemantics.sentence_correct
    (ModelTransfer.extensionality hL) (constructionSentence rho I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound pi inv c act ai zero root vertices chain names code codes order group)).mp
      (construction_models rho I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound pi inv c act ai zero root vertices chain names code codes order group hL hChoice)

def monotoneSentence {k : Nat} (rho : Fin 7 → Fin k) (I G F mul q bound labels E root w chain codes order : Fin k) : Project.Sentence where
  formula := Project.Formula.forallClosure k (ProjectSyntax.encode id
    (ForcingCohenRankConsumers.monotone (relation rho I G F mul q bound labels E root w chain codes order) id (rho 2) w codes))
  freeClosed := by simp [ProjectSyntax.freeClosed]

theorem monotone_models {k : Nat} (rho : Fin 7 → Fin k) (I G F mul q bound labels E root w chain codes order : Fin k)
    (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (monotoneSentence rho I G F mul q bound labels E root w chain codes order)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro env
  simp only [GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingCohenRankConsumers.monotone_semantics (M := M)]
  exact monotone hM env rho I G F mul q bound labels E root w chain codes order

theorem monotone_kernel_certificate {k : Nat} (rho : Fin 7 → Fin k) (I G F mul q bound labels E root w chain codes order : Fin k) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (monotoneSentence rho I G F mul q bound labels E root w chain codes order)) :=
  ModelTransfer.derives (fun _ hM => monotone_models rho I G F mul q bound labels E root w chain codes order hM)

end PPAC.Migration.ForcingCodeSelection
