/- Fixed OrdinalChoice.rootProbes and DiagramPlacements.RootProbes.
Consume the SAME completed AllIdeals/final Row at the singleton unit ideal;
no new saturation history, probe oracle or foundation is introduced. -/
import PPAC.Migration.ForcingChoiceFailure

namespace PPAC.Migration.ForcingRootProbes
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ForcingDiagramOrder (Product)
open ForcingDiagramPoset (LeftCancelMonoid Conical)
open ConstructionBaseMonoid (Divides)
open ConstructionProbeCones (JoinProperty)
open ForcingSupportSize (Injection Small)
open ForcingConcreteSystem (forcingRho)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 400000
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

/-- Literal source RootProbes, with an actual internal graph as its family. -/
def RootProbes (K D mul unit mark : M.Carrier .set) : Prop :=
  ∀ b, (Project.FirstOrderSemantics.reduct M).mem b D → b ≠ unit →
    ∃ family, Injection K D family ∧
      (∀ i p, PureKuratowski.PairMember M i p family → Product mul p b mark) ∧
      ∀ i j p q, PureKuratowski.PairMember M i p family → PureKuratowski.PairMember M j q family →
        i ≠ j → JoinProperty D mul p q mark

private theorem divides_unit {D mul unit x : M.Carrier .set}
    (hc : Conical D mul unit)
    (hx : (Project.FirstOrderSemantics.reduct M).mem x D) (hd : Divides D mul x unit) : x = unit := by
  obtain ⟨z,hz,hprod⟩ := hd
  exact (hc x z hx hz hprod).1

/-- Instantiate the existing ideal probes at the actual singleton unit ideal. -/
theorem of_ideal_probes (hM : FirstOrder.Theory.Models M nativeZF)
    {K D mul unit mark history kappa H C incoming base : M.Carrier .set}
    (hm : LeftCancelMonoid D mul unit) (hc : Conical D mul unit)
    (hMark : (Project.FirstOrderSemantics.reduct M).mem mark D)
    (hRow : ConstructionTowerHistory.Row history kappa D mul unit mark H C incoming base kappa)
    (hIdeals : ConstructionIdealProbes.AllIdeals K history kappa) : RootProbes K D mul unit mark := by
  obtain ⟨singleton,hSingle⟩ := ForcingWithTopCarrier.exists_single hM unit
  have hee : Divides D mul unit unit := ⟨unit,hm.1.1,(hm.1.2 unit hm.1.1 unit).1.mpr rfl⟩
  have hU : ConstructionIdealProbes.ConeIdeal D mul unit singleton := by
    refine ⟨?_,hm.1.1,⟨unit,(hSingle unit).mpr rfl⟩,?_,?_,?_⟩
    · intro x hx
      exact ((hSingle x).mp hx).symm ▸ hm.1.1
    · intro x hx
      have ex := (hSingle x).mp hx
      exact ex.symm ▸ hee
    · intro x y hx hy hxy
      have ey := (hSingle y).mp hy
      have ex := divides_unit hc hx (ey ▸ hxy)
      exact (hSingle x).mpr ex
    · intro x y z hx hy hz hJoin
      have ex := (hSingle x).mp hx
      have ey := (hSingle y).mp hy
      have hzdiv : Divides D mul z unit := (hJoin unit hm.1.1).mp ⟨ex.symm ▸ hee,ey.symm ▸ hee⟩
      exact (hSingle z).mpr (divides_unit hc hz hzdiv)
  intro b hb hne
  obtain ⟨family,hFamily,hProfiles,hIndependent⟩ := hIdeals D mul unit mark H C incoming base unit b singleton hRow hb hne hU
  refine ⟨family,hFamily,?_,?_⟩
  · intro i p hip
    obtain ⟨exit,_,hExit,hProduct,_⟩ := hProfiles i p hip
    have e := (hm.1.2 mark hMark exit).1.mp hExit
    exact e ▸ hProduct
  · intro i j p q hip hjq hij
    obtain ⟨exit,hExit,hJoin⟩ := hIndependent i j p q hip hjq hij
    have e := (hm.1.2 mark hMark exit).1.mp hExit
    exact e ▸ hJoin

/-- SAME concrete-system witnesses, using source saturation index mu (slot13),
not the separate Cohen bit-coordinate kappa (slot14). -/
theorem on_core (hM : FirstOrder.Theory.Models M nativeZF)
    (env : Fin 40 → M.Carrier .set) (hCore : ForcingConcreteSystem.Core hM env) :
    RootProbes (env 13) (env (forcingRho 0)) (env 18) (env 19) (env 20) ∧ ¬ Small (env 13) (env 39) := by
  obtain ⟨_,hm,_,_,_,_,_,_,_,_,_,hRow,_,_,_,_,hObject,_,_,hK,_,_,_,_,_,_,hKmu,_,hIdeals,_⟩ := hCore
  refine ⟨of_ideal_probes hM hm hObject.2.1 hObject.2.2.2.1 hRow hIdeals,?_⟩
  intro hmuW
  obtain ⟨f,hf⟩ := hKmu
  obtain ⟨g,hg⟩ := (ForcingSupportSize.native_small hM (env 13) (env 39)).mp hmuW
  exact hK ((ForcingSupportSize.native_small hM (env 14) (env 39)).mpr
    (ZF.exists_compositionInjection (ModelTransfer.project_models_iff.mp hM) (KuratowskiZF.interpretation hM) hf hg))

/-- Source graph equations and independent probe cones, all internally bound. -/
def witness {m : Nat} (K D mul mark b family : Fin m) : Project.Formula 1 m :=
  let up2 : Fin m → Fin (m+2) := fun j => j.succ.succ
  let up4 : Fin m → Fin (m+4) := fun j => j.succ.succ.succ.succ
  .conj (ProjectSyntax.encode id (Source.SetLanguage.injection family K D))
    (.conj
      (.forallE (.forallE (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge (up2 family) 1 0))
        (ProjectSyntax.encode id (ForcingDiagramOrder.product (up2 mul) 0 (up2 b) (up2 mark))))))
      (.forallE (.forallE (.forallE (.forallE
        (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge (up4 family) 3 1))
        (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge (up4 family) 2 0))
        (.imp (.neg (Project.Formula.extensionalEq (.bound 3) (.bound 2)))
          (ConstructionProbeCones.joinProperty (up4 D) (up4 mul) 1 0 (up4 mark))))))))))

def rootProbes {m : Nat} (K D mul unit mark : Fin m) : Project.Formula 1 m :=
  .forallE (.imp (.mem (.bound 0) (.bound D.succ))
    (.imp (.neg (Project.Formula.extensionalEq (.bound 0) (.bound unit.succ)))
      (.existsE (witness K.succ.succ D.succ.succ mul.succ.succ mark.succ.succ 1 0))))

theorem rootProbes_freeClosed {m : Nat} (K D mul unit mark : Fin m) : (rootProbes K D mul unit mark).FreeClosed := by
  simp -implicitDefEqProofs [rootProbes,witness,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
    ConstructionProbeCones.joinProperty_freeClosed]

theorem rootProbes_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (K D mul unit mark : Fin m) :
    Project.Formula.satisfies env (rootProbes K D mul unit mark) ↔
      RootProbes (env.bound K) (env.bound D) (env.bound mul) (env.bound unit) (env.bound mark) := by
  simp only [rootProbes,witness,RootProbes,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_mem_iff,
    Project.Formula.satisfies_neg_iff,Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM),
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ForcingSupportSize.injection_semantics,
    KuratowskiZF.source_edge,ForcingDiagramOrder.product_semantics,ConstructionProbeCones.joinProperty_semantics hM,
    Project.Term.eval_bound,id_eq]
  rfl

def outcomeFormula : Project.Formula 1 40 :=
  .conj (rootProbes 13 (forcingRho 0) 18 19 20)
    (.neg (ProjectSyntax.encode id (ForcingSupportSize.small (13 : Fin 40) 39)))

theorem outcomeFormula_freeClosed : outcomeFormula.FreeClosed := by
  simp -implicitDefEqProofs [outcomeFormula,Definitional.Formula.FreeClosed,rootProbes_freeClosed,ProjectSyntax.freeClosed]

theorem outcomeFormula_semantics (hM : FirstOrder.Theory.Models M nativeZF)
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 40) :
    Project.Formula.satisfies env outcomeFormula ↔
      RootProbes (env.bound 13) (env.bound (forcingRho 0)) (env.bound 18) (env.bound 19) (env.bound 20) ∧
      ¬ Small (env.bound 13) (env.bound 39) := by
  simp only [outcomeFormula,Project.Formula.satisfies_conj_iff,rootProbes_semantics hM,
    Project.Formula.satisfies_neg_iff,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingSupportSize.small_semantics,id_eq]

def sentence : Project.Sentence where
  formula := .existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE ((.conj ForcingConcreteSystem.coreFormula (.conj ForcingConcreteSystem.outcomeFormula (.conj ForcingNonwellorderableImage.imageOutcomeFormula (.conj ForcingChoiceFailure.outcomeFormula outcomeFormula))))))))))))))))))))))))))))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ForcingConcreteSystem.coreFormula_freeClosed,ForcingConcreteSystem.outcomeFormula_freeClosed,ForcingNonwellorderableImage.imageOutcomeFormula_freeClosed,ForcingChoiceFailure.outcomeFormula_freeClosed,outcomeFormula_freeClosed]

theorem models (hM : FirstOrder.Theory.Models M nativeZF)
    (hOrder : Project.Gw_order_d (InnerModel.Js_lt_d (M := Project.FirstOrderSemantics.reduct M)))
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) :
    (Project.fo_sentence sentence).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM)]
  intro free
  change Project.Formula.satisfies ({bound := Fin.elim0,free := free} :
    SetTheory.Env (Project.FirstOrderSemantics.reduct M) 0) sentence.formula
  obtain ⟨w,hw⟩ := ZF.exists_omega (ModelTransfer.project_models_iff.mp hM)
  obtain ⟨bound,labels,labelMap,F,G,W,Product,Y,X,CS,CC,I,outerF,P,base,incoming,C,H,mark,one,mul,D,history,stageBound,K,mu,continuum,Power,groundTop,u,seedC,seedH,values,Q,three,B,high,zero,seedMul,hCore,hOutcome⟩ := ForcingConcreteSystem.construct hM hOrder hChoice hw
  have hImages := ForcingNonwellorderableImage.on_core hM _ hCore hOutcome
  have hNotChoice := ForcingChoiceFailure.on_core hM hChoice _ hCore
  have hProbes := on_core hM _ hCore
  simp only [sentence,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    ForcingConcreteSystem.coreFormula_semantics hM,ForcingConcreteSystem.outcomeFormula_semantics hM,ForcingNonwellorderableImage.imageOutcomeFormula_semantics hM,ForcingChoiceFailure.outcomeFormula_semantics hM,outcomeFormula_semantics hM]
  exact ⟨w,bound,labels,labelMap,F,G,W,Product,Y,X,CS,CC,I,outerF,P,base,incoming,C,H,mark,one,mul,D,history,stageBound,K,mu,continuum,Power,groundTop,u,seedC,seedH,values,Q,three,B,high,zero,seedMul,hCore,hOutcome,hImages,hNotChoice,hProbes⟩

theorem kernel_certificate :
    FirstOrder.Derives nativeZF []
      (Project.fo_sentence (ConstructibleGround.relative (sentence))) := by
  apply ModelTransfer.derives
  intro M hM
  have hL := ConstructibleSource.model_zf hM
  have hRawChoice := (Project.FirstOrderSemantics.sentence_correct
    (ModelTransfer.extensionality hL) Axioms.choice).mp (ConstructibleSource.model_choice hM)
  obtain ⟨witness,_⟩ := ZF.exists_omega (ModelTransfer.project_models_iff.mp hL)
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct (ConstructibleSource.model hM)) 0 :=
    { bound := Fin.elim0, free := fun _ => witness }
  have hSat : Project.Formula.satisfies env (ConstructionDirectedCardinality.choice (m := 0)) := by
    change Project.Formula.satisfies env (Axioms.choice.formula.rename Fin.elim0)
    rw [Project.Formula.satisfies_rename]
    exact hRawChoice env.free
  have hChoice := (ConstructionDirectedCardinality.choice_semantics hL env).mp hSat
  apply ConstructibleGround.relative_models hM (sentence)
  exact (Project.FirstOrderSemantics.sentence_correct
    (ModelTransfer.extensionality hL) (sentence)).mp
      (models hL (ConstructionRoundSelection.l_order hM) hChoice)

end PPAC.Migration.ForcingRootProbes
