/- The exact old missed-cost supremum used by source HeightCost.uniform_margin.
Reuse native Separation and the accepted bounded union of internal cuts.
This canonicalizes the old bound for heightIntervals without object Choice. -/
import PPAC.Migration.ConstructionProbeIntervalsSyntax

namespace PPAC.Migration.ConstructionProbeCostSupremum
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionRealCuts ConstructionProbeIntervals ConstructionProbeLetterIntervals
open ConstructionBaseMonoid (Divides)
open ForcingSupportSize (MapsTo)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def CostMember (D mul C x y cd : M.Carrier .set) : Prop :=
  ∃ d, (Project.FirstOrderSemantics.reduct M).mem d D ∧ PureKuratowski.PairMember M d cd C ∧
    Divides D mul d y ∧ ¬ Divides D mul d x

def Family (D mul C x y family : M.Carrier .set) : Prop := ∀ cd,
  (Project.FirstOrderSemantics.reduct M).mem cd family ↔ CostMember D mul C x y cd

def Cap (D mul C x y cap : M.Carrier .set) : Prop := ∃ family,
  Family D mul C x y family ∧ UpperBound family cap ∧ ∀ t, UpperBound family t → Subset cap t

def costMember {m : Nat} (D mul C x y cd : Fin m) : Project.Formula 1 m :=
  .existsE (.conj (.mem (.bound 0) (.bound D.succ))
    (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge C.succ 0 cd.succ))
      (.conj (ProjectSyntax.encode id (ConstructionBaseMonoid.divides D.succ mul.succ 0 y.succ))
        (.neg (ProjectSyntax.encode id (ConstructionBaseMonoid.divides D.succ mul.succ 0 x.succ))))))

theorem costMember_freeClosed {m : Nat} (D mul C x y cd : Fin m) : (costMember D mul C x y cd).FreeClosed := by
  simp -implicitDefEqProofs [costMember,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed]

theorem costMember_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (D mul C x y cd : Fin m) :
    Project.Formula.satisfies env (costMember D mul C x y cd) ↔
      CostMember (env.bound D) (env.bound mul) (env.bound C) (env.bound x) (env.bound y) (env.bound cd) := by
  simp only [costMember,CostMember,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,
    ConstructionBaseMonoid.divides_semantics (M := M),Project.Formula.satisfies_neg_iff]
  rfl

def family {m : Nat} (D mul C x y f : Fin m) : Project.Formula 1 m :=
  .forallE (.iff (.mem (.bound 0) (.bound f.succ)) (costMember D.succ mul.succ C.succ x.succ y.succ 0))

theorem family_freeClosed {m : Nat} (D mul C x y f : Fin m) : (family D mul C x y f).FreeClosed := by
  simp -implicitDefEqProofs [family,Definitional.Formula.FreeClosed,costMember_freeClosed]

theorem family_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (D mul C x y f : Fin m) :
    Project.Formula.satisfies env (family D mul C x y f) ↔
      Family (env.bound D) (env.bound mul) (env.bound C) (env.bound x) (env.bound y) (env.bound f) := by
  simp only [family,Family,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_iff_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,costMember_semantics hM]
  rfl

def cap {m : Nat} (D mul C x y c : Fin m) : Project.Formula 1 m :=
  .existsE (.conj (family D.succ mul.succ C.succ x.succ y.succ 0) (ConstructionRealCuts.supremum 0 c.succ))

theorem cap_freeClosed {m : Nat} (D mul C x y c : Fin m) : (cap D mul C x y c).FreeClosed := by
  simp -implicitDefEqProofs [cap,Definitional.Formula.FreeClosed,family_freeClosed,ConstructionRealCuts.supremum_freeClosed]

theorem cap_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (D mul C x y c : Fin m) :
    Project.Formula.satisfies env (cap D mul C x y c) ↔
      Cap (env.bound D) (env.bound mul) (env.bound C) (env.bound x) (env.bound y) (env.bound c) := by
  simp only [cap,Cap,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    family_semantics hM,ConstructionRealCuts.supremum_semantics]
  rfl

theorem family_unique (hM : FirstOrder.Theory.Models M nativeZF) {D mul C x y f g : M.Carrier .set}
    (hf : Family D mul C x y f) (hg : Family D mul C x y g) : f = g :=
  (ModelTransfer.extensionality hM).eq_of_same_members f g (fun cd => (hf cd).trans (hg cd).symm)

theorem cap_unique (hM : FirstOrder.Theory.Models M nativeZF) {D mul C x y c d : M.Carrier .set}
    (hc : Cap D mul C x y c) (hd : Cap D mul C x y d) : c = d := by
  obtain ⟨f,hf,hUpper,hLeast⟩ := hc
  obtain ⟨g,hg,hUpper',hLeast'⟩ := hd
  have he := family_unique hM hf hg
  subst g
  have hcd := hLeast d hUpper'
  have hdc := hLeast' c hUpper
  exact (ModelTransfer.extensionality hM).eq_of_same_members c d (fun p => ⟨hcd p,hdc p⟩)

theorem exists_family (hM : FirstOrder.Theory.Models M nativeZF) {D mul C R x y : M.Carrier .set}
    (hC : MapsTo D R C) : ∃ f, Family D mul C x y f ∧ Subset f R := by
  let schema : Project.UnarySchema 5 := {
    body := costMember 1 2 3 4 5 0
    freeClosed := costMember_freeClosed _ _ _ _ _ _ }
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 5 := {
    bound := Fin.cases D (Fin.cases mul (Fin.cases C (Fin.cases x (fun _ => y)))), free := fun _ => D }
  obtain ⟨f,hf⟩ := ZF.separation_exists_d (ModelTransfer.project_models_iff.mp hM) schema env R
  have he : ∀ cd, Project.Formula.satisfies (env.push cd) schema.body ↔ CostMember D mul C x y cd :=
    fun cd => costMember_semantics hM (env.push cd) 1 2 3 4 5 0
  refine ⟨f,?_,fun cd hcd => ((hf cd).mp hcd).1⟩
  intro cd
  constructor
  · exact fun hcd => (he cd).mp ((hf cd).mp hcd).2
  · intro hcd
    have hcdCopy := hcd
    obtain ⟨d,_,hd,_,_⟩ := hcdCopy
    exact (hf cd).mpr ⟨hC.2 d cd hd,(he cd).mpr hcd⟩

/-- The old arbitrary uniform bound can be replaced by its actual missed-cost
supremum, retaining the strict gap and every missed-cost estimate. -/
theorem canonical_uniform (hM : FirstOrder.Theory.Models M nativeZF)
    {w Q R D mul C x y hx hy : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) (hQ : ConstructionFractionOrder.Carrier w Q)
    (hR : CutCarrier hM w Q R) (hC : MapsTo D R C) (hHX : Cut hM w Q hx)
    (hUniform : UniformAt hM w Q D mul C x y hx hy) :
    ∃ c tc, Cut hM w Q c ∧ Cap D mul C x y c ∧ ConstructionCutAddition.SumCut hM w Q hx c tc ∧
      Strict tc hy ∧ MissedBound D mul C x y c := by
  obtain ⟨old,oldTC,hOld,hOldSum,hRoom,hMissed⟩ := hUniform
  obtain ⟨f,hf,hfR⟩ := exists_family hM hC
  have hBound : UpperBound f old := by
    intro cd hcd
    obtain ⟨d,hd,hdc,hdy,hdx⟩ := (hf cd).mp hcd
    exact hMissed d cd hd hdc hdy hdx
  obtain ⟨c,hc,hu,hl⟩ := bounded_union hM hR hfR hOld hBound
  have hCLe := hl old hBound
  obtain ⟨tc,_,hSum⟩ := ConstructionCutArithmetic.exists_sum hM hw hQ hHX hc
  have hTCLe := ConstructionCutArithmetic.sum_mono hSum hOldSum (fun _ hp => hp) hCLe
  refine ⟨c,tc,hc,⟨f,hf,hu,hl⟩,hSum,le_strict_trans hTCLe hRoom,?_⟩
  intro d cd hd hdc hdy hdx
  exact hu cd ((hf cd).mpr ⟨d,hd,hdc,hdy,hdx⟩)

end PPAC.Migration.ConstructionProbeCostSupremum
