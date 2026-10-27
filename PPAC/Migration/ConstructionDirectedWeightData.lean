/- Pinned DirectLimits.height/cost/heightCost source input tables.
Reuse actual native function graphs, accepted cut weights and actual Cap.
Original stage conditions are explicit; no supplied limit weights or margins. -/
import PPAC.Migration.ConstructionDirectedProfiles
import PPAC.Migration.ConstructionProbeHeightCost

namespace PPAC.Migration.ConstructionDirectedWeightData
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionDirectedSystem
open ForcingSupportSize (MapsTo)
open ForcingConditionGraphs (FunctionOn)
open ForcingDiagramOrder (Product)
open ConstructionProbeCostSupremum (Cap)
open ConstructionProbeLetterIntervals (UniformMargins)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def WeightFamily (J Domains R Weights : M.Carrier .set) : Prop :=
  FunctionOn J Weights ∧ ∀ i D W, (Project.FirstOrderSemantics.reduct M).mem i J →
    PureKuratowski.PairMember M i D Domains → PureKuratowski.PairMember M i W Weights → MapsTo D R W

def Stable (J E Domains F Weights : M.Carrier .set) : Prop :=
  ∀ i j x y r Wi Wj, PureKuratowski.PairMember M i j E →
    Transition J Domains F i j x y → PureKuratowski.PairMember M i Wi Weights →
    PureKuratowski.PairMember M j Wj Weights → PureKuratowski.PairMember M x r Wi → PureKuratowski.PairMember M y r Wj

def HeightBounds (J Heights top : M.Carrier .set) : Prop := ∀ i H,
  (Project.FirstOrderSemantics.reduct M).mem i J → PureKuratowski.PairMember M i H Heights →
    ConstructionCutWeights.RangeBound top H

def CostBounds (J Costs top : M.Carrier .set) : Prop := ∀ i C,
  (Project.FirstOrderSemantics.reduct M).mem i J → PureKuratowski.PairMember M i C Costs →
    ConstructionProbeGateCap.Bounds top C

def UniformFamily (hM : FirstOrder.Theory.Models M nativeZF)
    (w Q J Domains Muls Heights Costs : M.Carrier .set) : Prop :=
  ∀ i D mul H C, (Project.FirstOrderSemantics.reduct M).mem i J →
    PureKuratowski.PairMember M i D Domains → PureKuratowski.PairMember M i mul Muls →
    PureKuratowski.PairMember M i H Heights → PureKuratowski.PairMember M i C Costs →
    UniformMargins hM w Q D mul H C

/-- Literal source hSup, as preservation of the SAME actual least upper bound. -/
def SupremumLaws (J E Domains F Muls Costs : M.Carrier .set) : Prop :=
  ∀ i j D1 D2 m1 m2 C1 C2 f, (Project.FirstOrderSemantics.reduct M).mem i J →
    (Project.FirstOrderSemantics.reduct M).mem j J → PureKuratowski.PairMember M i j E →
    PureKuratowski.PairMember M i D1 Domains → PureKuratowski.PairMember M j D2 Domains →
    PureKuratowski.PairMember M i m1 Muls → PureKuratowski.PairMember M j m2 Muls →
    PureKuratowski.PairMember M i C1 Costs → PureKuratowski.PairMember M j C2 Costs → Product F i j f →
    ∀ x y fx fy cap, PureKuratowski.PairMember M x fx f → PureKuratowski.PairMember M y fy f →
      Cap D1 m1 C1 x y cap → Cap D2 m2 C2 fx fy cap



def weightFamily {m : Nat} (J Domains R Weights : Fin m) : Project.Formula 1 m :=
  (.conj (ProjectSyntax.encode id (Source.SetLanguage.functionOn Weights J)) (.forallE (.forallE (.forallE
  (.imp (.mem (.bound (2 : Fin (m+3))) (.bound J.succ.succ.succ)) (.imp (ProjectSyntax.encode id
  (Source.SetLanguage.edge Domains.succ.succ.succ (2 : Fin (m+3)) (1 : Fin (m+3)))) (.imp
  (ProjectSyntax.encode id (Source.SetLanguage.edge Weights.succ.succ.succ (2 : Fin (m+3)) (0 : Fin (m+3))))
  (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (0 : Fin (m+3)) (1 : Fin (m+3))
  R.succ.succ.succ)))))))))

theorem weightFamily_freeClosed {m : Nat} (J Domains R Weights : Fin m) :
    (weightFamily J Domains R Weights).FreeClosed := by
  simp -implicitDefEqProofs [weightFamily,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed]

theorem weightFamily_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (J Domains R Weights : Fin m) :
    Project.Formula.satisfies env (weightFamily J Domains R Weights) ↔ WeightFamily (env.bound J) (env.bound Domains) (env.bound R) (env.bound Weights) := by
  simp only [weightFamily,WeightFamily,Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,ForcingConditionGraphs.functionOn_semantics,ForcingSupportSize.mapsTo_semantics (M := M)]
  rfl


def stable {m : Nat} (J E Domains F Weights : Fin m) : Project.Formula 1 m :=
  (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE (.imp (ProjectSyntax.encode id
  (Source.SetLanguage.edge E.succ.succ.succ.succ.succ.succ.succ (6 : Fin (m+7)) (5 : Fin (m+7)))) (.imp
  (ConstructionDirectedSystem.transition J.succ.succ.succ.succ.succ.succ.succ
  Domains.succ.succ.succ.succ.succ.succ.succ F.succ.succ.succ.succ.succ.succ.succ (6 : Fin (m+7)) (5 : Fin
  (m+7)) (4 : Fin (m+7)) (3 : Fin (m+7))) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge
  Weights.succ.succ.succ.succ.succ.succ.succ (6 : Fin (m+7)) (1 : Fin (m+7)))) (.imp (ProjectSyntax.encode
  id (Source.SetLanguage.edge Weights.succ.succ.succ.succ.succ.succ.succ (5 : Fin (m+7)) (0 : Fin (m+7))))
  (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge (1 : Fin (m+7)) (4 : Fin (m+7)) (2 : Fin (m+7))))
  (ProjectSyntax.encode id (Source.SetLanguage.edge (0 : Fin (m+7)) (3 : Fin (m+7)) (2 : Fin
  (m+7))))))))))))))))

theorem stable_freeClosed {m : Nat} (J E Domains F Weights : Fin m) :
    (stable J E Domains F Weights).FreeClosed := by
  simp -implicitDefEqProofs [stable,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,ConstructionDirectedSystem.transition_freeClosed]

theorem stable_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (J E Domains F Weights : Fin m) :
    Project.Formula.satisfies env (stable J E Domains F Weights) ↔ Stable (env.bound J) (env.bound E) (env.bound Domains) (env.bound F) (env.bound Weights) := by
  simp only [stable,Stable,Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_imp_iff,
    
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,ConstructionDirectedSystem.transition_semantics hM]
  rfl


def heightBounds {m : Nat} (J Heights top : Fin m) : Project.Formula 1 m :=
  (.forallE (.forallE (.imp (.mem (.bound (1 : Fin (m+2))) (.bound J.succ.succ)) (.imp (ProjectSyntax.encode
  id (Source.SetLanguage.edge Heights.succ.succ (1 : Fin (m+2)) (0 : Fin (m+2))))
  (ConstructionCutWeights.rangeBound top.succ.succ (0 : Fin (m+2)))))))

theorem heightBounds_freeClosed {m : Nat} (J Heights top : Fin m) :
    (heightBounds J Heights top).FreeClosed := by
  simp -implicitDefEqProofs [heightBounds,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,ConstructionCutWeights.rangeBound_freeClosed]

theorem heightBounds_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (J Heights top : Fin m) :
    Project.Formula.satisfies env (heightBounds J Heights top) ↔ HeightBounds (env.bound J) (env.bound Heights) (env.bound top) := by
  simp only [heightBounds,HeightBounds,Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,ConstructionCutWeights.rangeBound_semantics hM]
  rfl


def costBounds {m : Nat} (J Costs top : Fin m) : Project.Formula 1 m :=
  (.forallE (.forallE (.imp (.mem (.bound (1 : Fin (m+2))) (.bound J.succ.succ)) (.imp (ProjectSyntax.encode
  id (Source.SetLanguage.edge Costs.succ.succ (1 : Fin (m+2)) (0 : Fin (m+2))))
  (ConstructionProbeGateCap.bounds top.succ.succ (0 : Fin (m+2)))))))

theorem costBounds_freeClosed {m : Nat} (J Costs top : Fin m) :
    (costBounds J Costs top).FreeClosed := by
  simp -implicitDefEqProofs [costBounds,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,ConstructionProbeGateCap.bounds_freeClosed]

theorem costBounds_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (J Costs top : Fin m) :
    Project.Formula.satisfies env (costBounds J Costs top) ↔ CostBounds (env.bound J) (env.bound Costs) (env.bound top) := by
  simp only [costBounds,CostBounds,Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,ConstructionProbeGateCap.bounds_semantics hM]
  rfl


def uniformFamily {m : Nat} (w Q J Domains Muls Heights Costs : Fin m) : Project.Formula 1 m :=
  (.forallE (.forallE (.forallE (.forallE (.forallE (.imp (.mem (.bound (4 : Fin (m+5))) (.bound
  J.succ.succ.succ.succ.succ)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge
  Domains.succ.succ.succ.succ.succ (4 : Fin (m+5)) (3 : Fin (m+5)))) (.imp (ProjectSyntax.encode id
  (Source.SetLanguage.edge Muls.succ.succ.succ.succ.succ (4 : Fin (m+5)) (2 : Fin (m+5)))) (.imp
  (ProjectSyntax.encode id (Source.SetLanguage.edge Heights.succ.succ.succ.succ.succ (4 : Fin (m+5)) (1 :
  Fin (m+5)))) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge Costs.succ.succ.succ.succ.succ (4 :
  Fin (m+5)) (0 : Fin (m+5)))) (ConstructionProbeIntervalsSyntax.uniformMargins w.succ.succ.succ.succ.succ
  Q.succ.succ.succ.succ.succ (3 : Fin (m+5)) (2 : Fin (m+5)) (1 : Fin (m+5)) (0 : Fin (m+5)))))))))))))

theorem uniformFamily_freeClosed {m : Nat} (w Q J Domains Muls Heights Costs : Fin m) :
    (uniformFamily w Q J Domains Muls Heights Costs).FreeClosed := by
  simp -implicitDefEqProofs [uniformFamily,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,ConstructionProbeIntervalsSyntax.uniformMargins_freeClosed]

theorem uniformFamily_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w Q J Domains Muls Heights Costs : Fin m) :
    Project.Formula.satisfies env (uniformFamily w Q J Domains Muls Heights Costs) ↔ UniformFamily hM (env.bound w) (env.bound Q) (env.bound J) (env.bound Domains) (env.bound Muls) (env.bound Heights) (env.bound Costs) := by
  simp only [uniformFamily,UniformFamily,Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,ConstructionProbeIntervalsSyntax.uniformMargins_semantics hM]
  rfl


def supremumLaws {m : Nat} (J E Domains F Muls Costs : Fin m) : Project.Formula 1 m :=
  (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE (.imp (.mem
  (.bound (8 : Fin (m+9))) (.bound J.succ.succ.succ.succ.succ.succ.succ.succ.succ)) (.imp (.mem (.bound (7 :
  Fin (m+9))) (.bound J.succ.succ.succ.succ.succ.succ.succ.succ.succ)) (.imp (ProjectSyntax.encode id
  (Source.SetLanguage.edge E.succ.succ.succ.succ.succ.succ.succ.succ.succ (8 : Fin (m+9)) (7 : Fin (m+9))))
  (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge
  Domains.succ.succ.succ.succ.succ.succ.succ.succ.succ (8 : Fin (m+9)) (6 : Fin (m+9)))) (.imp
  (ProjectSyntax.encode id (Source.SetLanguage.edge Domains.succ.succ.succ.succ.succ.succ.succ.succ.succ (7
  : Fin (m+9)) (5 : Fin (m+9)))) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge
  Muls.succ.succ.succ.succ.succ.succ.succ.succ.succ (8 : Fin (m+9)) (4 : Fin (m+9)))) (.imp
  (ProjectSyntax.encode id (Source.SetLanguage.edge Muls.succ.succ.succ.succ.succ.succ.succ.succ.succ (7 :
  Fin (m+9)) (3 : Fin (m+9)))) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge
  Costs.succ.succ.succ.succ.succ.succ.succ.succ.succ (8 : Fin (m+9)) (2 : Fin (m+9)))) (.imp
  (ProjectSyntax.encode id (Source.SetLanguage.edge Costs.succ.succ.succ.succ.succ.succ.succ.succ.succ (7 :
  Fin (m+9)) (1 : Fin (m+9)))) (.imp (ProjectSyntax.encode id (ForcingDiagramOrder.product
  F.succ.succ.succ.succ.succ.succ.succ.succ.succ (8 : Fin (m+9)) (7 : Fin (m+9)) (0 : Fin (m+9)))) (.forallE
  (.forallE (.forallE (.forallE (.forallE (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge (0 : Fin
  (m+9)).succ.succ.succ.succ.succ (4 : Fin (m+14)) (2 : Fin (m+14)))) (.imp (ProjectSyntax.encode id
  (Source.SetLanguage.edge (0 : Fin (m+9)).succ.succ.succ.succ.succ (3 : Fin (m+14)) (1 : Fin (m+14))))
  (.imp (ConstructionProbeCostSupremum.cap (6 : Fin (m+9)).succ.succ.succ.succ.succ (4 : Fin
  (m+9)).succ.succ.succ.succ.succ (2 : Fin (m+9)).succ.succ.succ.succ.succ (4 : Fin (m+14)) (3 : Fin (m+14))
  (0 : Fin (m+14))) (ConstructionProbeCostSupremum.cap (5 : Fin (m+9)).succ.succ.succ.succ.succ (3 : Fin
  (m+9)).succ.succ.succ.succ.succ (1 : Fin (m+9)).succ.succ.succ.succ.succ (2 : Fin (m+14)) (1 : Fin (m+14))
  (0 : Fin (m+14))))))))))))))))))))))))))))))

theorem supremumLaws_freeClosed {m : Nat} (J E Domains F Muls Costs : Fin m) :
    (supremumLaws J E Domains F Muls Costs).FreeClosed := by
  simp -implicitDefEqProofs [supremumLaws,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,ConstructionProbeCostSupremum.cap_freeClosed]

theorem supremumLaws_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (J E Domains F Muls Costs : Fin m) :
    Project.Formula.satisfies env (supremumLaws J E Domains F Muls Costs) ↔ SupremumLaws (env.bound J) (env.bound E) (env.bound Domains) (env.bound F) (env.bound Muls) (env.bound Costs) := by
  simp only [supremumLaws,SupremumLaws,Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,ForcingDiagramOrder.product_semantics (M := M),ConstructionProbeCostSupremum.cap_semantics hM]
  rfl

end PPAC.Migration.ConstructionDirectedWeightData
