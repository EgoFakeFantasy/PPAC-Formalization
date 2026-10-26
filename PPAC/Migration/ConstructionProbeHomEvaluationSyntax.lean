/- Pure source evalHom relation and its actual Word-domain map. -/
import PPAC.Migration.ConstructionProbeHomEvaluation
import PPAC.Migration.ConstructionProbeWord

namespace PPAC.Migration.ConstructionProbeHomEvaluationSyntax
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionProbeHomEvaluation ConstructionProbeRaw
open ConstructionProbeWord (WordCarrier word_raw)
open ConstructionProbeLetters (Representatives)
open ForcingSupportSize (MapsTo)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def history {m : Nat} (w N mulN F Q f x H n : Fin m) : Project.Formula 1 m :=
  Project.Formula.isRecursiveSequenceIn PureKuratowskiProject.convention
    (stepSchema w N mulN F Q f x)
    (Definitional.TermVector.boundParameters m 0) (.bound H) (.bound n) (.bound N)

theorem history_freeClosed {m : Nat} (w N mulN F Q f x H n : Fin m) :
    (history w N mulN F Q f x H n).FreeClosed := by
  apply Project.Formula.isRecursiveSequenceIn_freeClosed
  all_goals simp

theorem history_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m)
    (w N mulN F Q f x H n : Fin m) :
    Project.Formula.satisfies env (history w N mulN F Q f x H n) ↔
      History hM (env.bound w) (env.bound N) (env.bound mulN) (env.bound F)
        (env.bound Q) (env.bound f) (env.bound x) (env.bound H) (env.bound n) := by
  rw [history,Project.Formula.satisfies_isRecursiveSequenceIn_iff
    (KuratowskiZF.interpretation hM) (ModelTransfer.project_models_iff.mp hM).1,
    Definitional.TermVector.evalEnv_boundParameters_zero]
  have he : (stepSchema w N mulN F Q f x).denote env =
      Step (env.bound w) (env.bound N) (env.bound mulN) (env.bound F)
        (env.bound Q) (env.bound f) (env.bound x) := by
    funext H y
    exact propext (stepSchema_semantics hM env w N mulN F Q f x H y)
  rw [he]
  rfl

def eval {m : Nat} (w D S N mulN F Q q y : Fin m) : Project.Formula 1 m :=
  (.existsE (.existsE (.existsE (.existsE (.existsE (.conj (.mem (.bound 4) (.bound
    w.succ.succ.succ.succ.succ)) (.conj (.mem (.bound 3) (.bound w.succ.succ.succ.succ.succ)) (.conj
    (Project.Formula.isSuccessor (.bound 3) (.bound 4)) (.conj (ProjectSyntax.encode id
    (Source.SetLanguage.mapsTo 2 4 S.succ.succ.succ.succ.succ)) (.conj (.mem (.bound 1) (.bound
    D.succ.succ.succ.succ.succ)) (.conj (ProjectSyntax.encode id (PairSyntax.ordered
    q.succ.succ.succ.succ.succ 2 1)) (.conj (history w.succ.succ.succ.succ.succ N.succ.succ.succ.succ.succ
    mulN.succ.succ.succ.succ.succ F.succ.succ.succ.succ.succ Q.succ.succ.succ.succ.succ 2 1 0 3)
    (ProjectSyntax.encode id (Source.SetLanguage.edge 0 4 y.succ.succ.succ.succ.succ))))))))))))))

theorem eval_freeClosed {m : Nat} (w D S N mulN F Q q y : Fin m) : (eval w D S N mulN F Q q y).FreeClosed := by
  simp -implicitDefEqProofs [eval,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,history_freeClosed,
    Project.Formula.isSuccessor,Project.Formula.extensionalEq_freeClosed_iff]

theorem eval_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w D S N mulN F Q q y : Fin m) :
    Project.Formula.satisfies env (eval w D S N mulN F Q q y) ↔
      Eval hM (env.bound w) (env.bound D) (env.bound S) (env.bound N) (env.bound mulN)
        (env.bound F) (env.bound Q) (env.bound q) (env.bound y) := by
  simp only [eval,Eval,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,Project.Formula.satisfies_isSuccessor_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingSupportSize.mapsTo_semantics (M := M),KuratowskiZF.source_code,KuratowskiZF.source_edge,history_semantics hM]
  rfl

def LiftGraph (hM : FirstOrder.Theory.Models M nativeZF) (w D S N mulN F Q W L : M.Carrier .set) : Prop :=
  ∀ q y, PureKuratowski.PairMember M q y L ↔
    (Project.FirstOrderSemantics.reduct M).mem q W ∧ Eval hM w D S N mulN F Q q y

theorem exists_lift_graph (hM : FirstOrder.Theory.Models M nativeZF)
    {w D S N J mulN F Q mul A b W : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hJ : Representatives N N J) (hMul : MapsTo J N mulN) (hF : MapsTo D N F) (hQ : MapsTo S N Q)
    (hW : WordCarrier w D S mul A b W) : ∃ L, MapsTo W N L ∧ LiftGraph hM w D S N mulN F Q W L := by
  let schema : Project.BinarySchema 7 := {
    body := eval 2 3 4 5 6 7 8 1 0
    freeClosed := eval_freeClosed _ _ _ _ _ _ _ _ _ }
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 7 := {
    bound := Fin.cases w (Fin.cases D (Fin.cases S (Fin.cases N (Fin.cases mulN (Fin.cases F (fun _ => Q)))))),
    free := fun _ => w }
  have he (q y : M.Carrier .set) : schema.denote env q y ↔ Eval hM w D S N mulN F Q q y :=
    eval_semantics hM ((env.push q).push y) 2 3 4 5 6 7 8 1 0
  obtain ⟨L,hL,hgraph⟩ := ZF.exists_setFunctionFromTo_of_denote (ModelTransfer.project_models_iff.mp hM)
    (KuratowskiZF.interpretation hM) schema env (source := W) (target := N) (by
      intro q hq
      obtain ⟨y,hy⟩ := eval_total hM hw hJ hMul hF hQ (word_raw hW hq)
      exact ⟨y,(he q y).mpr hy⟩) (by
      intro q _ y z hy hz
      exact eval_unique hM hw hJ hMul hF hQ ((he q y).mp hy) ((he q z).mp hz)) (by
      intro q y _ hy
      exact eval_range hM ((he q y).mp hy))
  refine ⟨L,(ForcingSupportSize.native_mapsTo hM W N L).mpr hL,fun q y => ?_⟩
  exact (hgraph q y).trans (and_congr_right (fun _ => he q y))

end PPAC.Migration.ConstructionProbeHomEvaluationSyntax
