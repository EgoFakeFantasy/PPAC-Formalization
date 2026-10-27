/- Pinned original Probe/Merger normal forms, reused as SOURCE contracts.
Keep the SAME alphabet/path/quotient/action/product/root graphs needed by
probe_gate and cone_realization; these are actual formulas, not proof tags.
Consumers: stronger original parent bridge and SAME selected Candidate/tower. -/
import PPAC.Migration.ConstructionProbeSuccessor
import PPAC.Migration.ConstructionProbeWordMonoidSyntax
import PPAC.Migration.ConstructionProbeGeneratorSyntax
import PPAC.Migration.ConstructionProbeIndexedGeneratorsSyntax
import PPAC.Migration.ConstructionMergerRoots

namespace PPAC.Migration.ConstructionOperationSource
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ForcingSupportSize (MapsTo)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def Alpha (w D mul e zero mark a node S A E projection : M.Carrier .set) : Prop :=
  ∃ I K factor T CRep,
    ConstructionProbeAlphabet.Alphabet D mul e S I A E ∧
    ConstructionProbeCones.ConeLaws w D mul e zero node factor S projection A ∧
    MapsTo S D K ∧ ConstructionProbePath.FactorTable w D mul node factor ∧ MapsTo w D T ∧
    ConstructionProbePath.TerminalTable w D mul node a T ∧
    ConstructionProbeTarget.TargetLaws mul projection T A K ∧ ConstructionProbeAlphabet.ExitGraph mul K mark E ∧
    ConstructionProbeLetters.Representatives w D CRep ∧ MapsTo CRep S projection ∧
    ConstructionProbeLetters.Letters w D mul factor CRep S ∧
    ConstructionProbeLetters.Projection w D mul factor CRep projection ∧
    ConstructionProbeAction.ActionTable D mul projection A

def Probe (hM : FirstOrder.Theory.Models M nativeZF)
    (w D mul e zero mark a b node W G unit O gen : M.Carrier .set) : Prop :=
  ConstructionProbePath.Path w D mul e zero a node ∧
  (Project.FirstOrderSemantics.reduct M).mem b D ∧ b ≠ e ∧
  ∃ S A E projection KG P,
    Alpha w D mul e zero mark a node S A E projection ∧
    ConstructionProbeWord.WordCarrier w D S mul A b W ∧ ConstructionProbeRaw.Old zero D e unit ∧
    ConstructionProbeWordMonoid.MultiplicationGraph hM w D S zero mul A b W E G ∧
    ConstructionProbeOldEmbedding.OldGraph zero D O ∧ MapsTo S W KG ∧
    ConstructionProbeGenerator.GeneratorGraph w D S unit KG ∧ MapsTo w W P ∧
    ConstructionProbeIndexedGenerators.ProbeGraph w projection e KG P ∧ PureKuratowski.PairMember M zero gen P

def Merger (w n D mul e zero P W G unit O roots : M.Carrier .set) : Prop :=
  ConstructionMergerRelations.Prescription n D P ∧ ConstructionMergerRelations.Valid n D mul P ∧
  ∃ C L projection K A I T B,
    ConstructionProbeLetters.Representatives n D C ∧ MapsTo C L projection ∧
    ConstructionMergerCopies.Copies n D mul P C L ∧ ConstructionMergerCopies.Projection n D mul P C projection ∧
    ConstructionMergerCopies.EqualityLaw n D mul P projection ∧
    ConstructionProbeLetters.Representatives L D K ∧ MapsTo K L A ∧
    ConstructionMergerAction.ActionTable D mul projection A ∧ ConstructionMergerAction.RightFreeAction mul e L A ∧
    ConstructionMergerAction.CopyLaw D mul projection A ∧ ConstructionProbeRaw.Carrier w D L W ∧
    ConstructionProbeLetters.Representatives W D I ∧ MapsTo I W T ∧
    ConstructionMergerWordAction.ActionTable w D L zero mul A T ∧ ConstructionMergerAction.RightFreeAction mul e W T ∧
    ConstructionProbeLetters.Representatives W W B ∧ MapsTo B W G ∧ ConstructionMergerWordProduct.Laws w D L zero T G ∧
    ConstructionProbeRaw.Old zero D e unit ∧ ConstructionProbeOldEmbedding.OldGraph zero D O ∧
    ConstructionMergerRoots.RootGraph w D L e projection unit roots ∧
    ConstructionMergerRoots.RootLaws w D L n mul P projection unit G O roots



def alpha {m : Nat} (w D mul e zero mark a node S A E projection : Fin m) : Project.Formula 1 m :=
  (.existsE (.existsE (.existsE (.existsE (.existsE (.conj (ConstructionProbeAlphabet.alphabet
  D.succ.succ.succ.succ.succ mul.succ.succ.succ.succ.succ e.succ.succ.succ.succ.succ
  S.succ.succ.succ.succ.succ (4 : Fin (m+5)) A.succ.succ.succ.succ.succ E.succ.succ.succ.succ.succ) (.conj
  (ConstructionProbeCones.coneLaws w.succ.succ.succ.succ.succ D.succ.succ.succ.succ.succ
  mul.succ.succ.succ.succ.succ e.succ.succ.succ.succ.succ zero.succ.succ.succ.succ.succ
  node.succ.succ.succ.succ.succ (2 : Fin (m+5)) S.succ.succ.succ.succ.succ
  projection.succ.succ.succ.succ.succ A.succ.succ.succ.succ.succ) (.conj (ProjectSyntax.encode id
  (Source.SetLanguage.mapsTo (3 : Fin (m+5)) S.succ.succ.succ.succ.succ D.succ.succ.succ.succ.succ)) (.conj
  (ConstructionProbePath.factorTable w.succ.succ.succ.succ.succ D.succ.succ.succ.succ.succ
  mul.succ.succ.succ.succ.succ node.succ.succ.succ.succ.succ (2 : Fin (m+5))) (.conj (ProjectSyntax.encode
  id (Source.SetLanguage.mapsTo (1 : Fin (m+5)) w.succ.succ.succ.succ.succ D.succ.succ.succ.succ.succ))
  (.conj (ConstructionProbePath.terminalTable w.succ.succ.succ.succ.succ D.succ.succ.succ.succ.succ
  mul.succ.succ.succ.succ.succ node.succ.succ.succ.succ.succ a.succ.succ.succ.succ.succ (1 : Fin (m+5)))
  (.conj (ConstructionProbeTarget.targetLaws mul.succ.succ.succ.succ.succ
  projection.succ.succ.succ.succ.succ (1 : Fin (m+5)) A.succ.succ.succ.succ.succ (3 : Fin (m+5))) (.conj
  (ConstructionProbeAlphabet.exitGraph mul.succ.succ.succ.succ.succ (3 : Fin (m+5))
  mark.succ.succ.succ.succ.succ E.succ.succ.succ.succ.succ) (.conj (ConstructionProbeLetters.representatives
  w.succ.succ.succ.succ.succ D.succ.succ.succ.succ.succ (0 : Fin (m+5))) (.conj (ProjectSyntax.encode id
  (Source.SetLanguage.mapsTo projection.succ.succ.succ.succ.succ (0 : Fin (m+5))
  S.succ.succ.succ.succ.succ)) (.conj (ConstructionProbeLetters.letters w.succ.succ.succ.succ.succ
  D.succ.succ.succ.succ.succ mul.succ.succ.succ.succ.succ (2 : Fin (m+5)) (0 : Fin (m+5))
  S.succ.succ.succ.succ.succ) (.conj (ConstructionProbeLetters.projectionGraph w.succ.succ.succ.succ.succ
  D.succ.succ.succ.succ.succ mul.succ.succ.succ.succ.succ (2 : Fin (m+5)) (0 : Fin (m+5))
  projection.succ.succ.succ.succ.succ) (ConstructionProbeAction.actionTable D.succ.succ.succ.succ.succ
  mul.succ.succ.succ.succ.succ projection.succ.succ.succ.succ.succ
  A.succ.succ.succ.succ.succ))))))))))))))))))

theorem alpha_freeClosed {m : Nat} (w D mul e zero mark a node S A E projection : Fin m) :
    (alpha w D mul e zero mark a node S A E projection).FreeClosed := by
  simp -implicitDefEqProofs [alpha,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,ConstructionProbeAlphabet.alphabet_freeClosed,ConstructionProbeCones.coneLaws_freeClosed,ConstructionProbePath.factorTable_freeClosed,ConstructionProbePath.terminalTable_freeClosed,ConstructionProbeTarget.targetLaws_freeClosed,ConstructionProbeAlphabet.exitGraph_freeClosed,ConstructionProbeLetters.representatives_freeClosed,ConstructionProbeLetters.letters_freeClosed,ConstructionProbeLetters.projectionGraph_freeClosed,ConstructionProbeAction.actionTable_freeClosed]

theorem alpha_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w D mul e zero mark a node S A E projection : Fin m) :
    Project.Formula.satisfies env (alpha w D mul e zero mark a node S A E projection) ↔ Alpha (env.bound w) (env.bound D) (env.bound mul) (env.bound e) (env.bound zero) (env.bound mark) (env.bound a) (env.bound node) (env.bound S) (env.bound A) (env.bound E) (env.bound projection) := by
  simp only [alpha,Alpha,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff,
    
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ConstructionProbeAlphabet.alphabet_semantics hM,ConstructionProbeCones.coneLaws_semantics hM,ConstructionProbePath.factorTable_semantics hM,ConstructionProbePath.terminalTable_semantics hM,ConstructionProbeTarget.targetLaws_semantics hM,ConstructionProbeAlphabet.exitGraph_semantics hM,ConstructionProbeLetters.representatives_semantics hM,ConstructionProbeLetters.letters_semantics hM,ConstructionProbeLetters.projectionGraph_semantics hM,ConstructionProbeAction.actionTable_semantics hM,ForcingSupportSize.mapsTo_semantics (M := M)]
  rfl

def probe {m : Nat} (w D mul e zero mark a b node W G unit O gen : Fin m) : Project.Formula 1 m :=
  (.conj (ConstructionProbePath.path w D mul e zero a node) (.conj (.mem (.bound b) (.bound D)) (.conj (.neg
  (Project.Formula.extensionalEq (.bound b) (.bound e))) (.existsE (.existsE (.existsE (.existsE (.existsE
  (.existsE (.conj (alpha w.succ.succ.succ.succ.succ.succ D.succ.succ.succ.succ.succ.succ
  mul.succ.succ.succ.succ.succ.succ e.succ.succ.succ.succ.succ.succ zero.succ.succ.succ.succ.succ.succ
  mark.succ.succ.succ.succ.succ.succ a.succ.succ.succ.succ.succ.succ node.succ.succ.succ.succ.succ.succ (5 :
  Fin (m+6)) (4 : Fin (m+6)) (3 : Fin (m+6)) (2 : Fin (m+6))) (.conj (ConstructionProbeWord.wordCarrier
  w.succ.succ.succ.succ.succ.succ D.succ.succ.succ.succ.succ.succ (5 : Fin (m+6))
  mul.succ.succ.succ.succ.succ.succ (4 : Fin (m+6)) b.succ.succ.succ.succ.succ.succ
  W.succ.succ.succ.succ.succ.succ) (.conj (ConstructionProbeRaw.old zero.succ.succ.succ.succ.succ.succ
  D.succ.succ.succ.succ.succ.succ e.succ.succ.succ.succ.succ.succ unit.succ.succ.succ.succ.succ.succ) (.conj
  (ConstructionProbeWordMonoidSyntax.multiplicationGraph w.succ.succ.succ.succ.succ.succ
  D.succ.succ.succ.succ.succ.succ (5 : Fin (m+6)) zero.succ.succ.succ.succ.succ.succ
  mul.succ.succ.succ.succ.succ.succ (4 : Fin (m+6)) b.succ.succ.succ.succ.succ.succ
  W.succ.succ.succ.succ.succ.succ (3 : Fin (m+6)) G.succ.succ.succ.succ.succ.succ) (.conj
  (ConstructionProbeOldEmbeddingSyntax.oldGraph zero.succ.succ.succ.succ.succ.succ
  D.succ.succ.succ.succ.succ.succ O.succ.succ.succ.succ.succ.succ) (.conj (ProjectSyntax.encode id
  (Source.SetLanguage.mapsTo (1 : Fin (m+6)) (5 : Fin (m+6)) W.succ.succ.succ.succ.succ.succ)) (.conj
  (ConstructionProbeGeneratorSyntax.generatorGraph w.succ.succ.succ.succ.succ.succ
  D.succ.succ.succ.succ.succ.succ (5 : Fin (m+6)) unit.succ.succ.succ.succ.succ.succ (1 : Fin (m+6))) (.conj
  (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (0 : Fin (m+6)) w.succ.succ.succ.succ.succ.succ
  W.succ.succ.succ.succ.succ.succ)) (.conj (ConstructionProbeIndexedGeneratorsSyntax.probeGraph
  w.succ.succ.succ.succ.succ.succ (2 : Fin (m+6)) e.succ.succ.succ.succ.succ.succ (1 : Fin (m+6)) (0 : Fin
  (m+6))) (ProjectSyntax.encode id (Source.SetLanguage.edge (0 : Fin (m+6))
  zero.succ.succ.succ.succ.succ.succ gen.succ.succ.succ.succ.succ.succ))))))))))))))))))))

theorem probe_freeClosed {m : Nat} (w D mul e zero mark a b node W G unit O gen : Fin m) :
    (probe w D mul e zero mark a b node W G unit O gen).FreeClosed := by
  simp -implicitDefEqProofs [probe,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,ConstructionProbePath.path_freeClosed,Project.Formula.extensionalEq,alpha_freeClosed,ConstructionProbeWord.wordCarrier_freeClosed,ConstructionProbeRaw.old_freeClosed,ConstructionProbeWordMonoidSyntax.multiplicationGraph_freeClosed,ConstructionProbeOldEmbeddingSyntax.oldGraph_freeClosed,ConstructionProbeGeneratorSyntax.generatorGraph_freeClosed,ConstructionProbeIndexedGeneratorsSyntax.probeGraph_freeClosed]

theorem probe_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w D mul e zero mark a b node W G unit O gen : Fin m) :
    Project.Formula.satisfies env (probe w D mul e zero mark a b node W G unit O gen) ↔ Probe hM (env.bound w) (env.bound D) (env.bound mul) (env.bound e) (env.bound zero) (env.bound mark) (env.bound a) (env.bound b) (env.bound node) (env.bound W) (env.bound G) (env.bound unit) (env.bound O) (env.bound gen) := by
  simp only [probe,Probe,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_neg_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,ConstructionProbePath.path_semantics hM,Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM),alpha_semantics hM,ConstructionProbeWord.wordCarrier_semantics hM,ConstructionProbeRaw.old_semantics hM,ConstructionProbeWordMonoidSyntax.multiplicationGraph_semantics hM,ConstructionProbeOldEmbeddingSyntax.oldGraph_semantics hM,ConstructionProbeGeneratorSyntax.generatorGraph_semantics hM,ConstructionProbeIndexedGeneratorsSyntax.probeGraph_semantics hM,ForcingSupportSize.mapsTo_semantics (M := M)]
  rfl


def merger {m : Nat} (w n D mul e zero P W G unit O roots : Fin m) : Project.Formula 1 m :=
  (.conj (ConstructionMergerRelations.prescription n D P) (.conj (ConstructionMergerRelations.valid n D mul P)
  (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.conj
  (ConstructionProbeLetters.representatives n.succ.succ.succ.succ.succ.succ.succ.succ
  D.succ.succ.succ.succ.succ.succ.succ.succ (7 : Fin (m+8))) (.conj (ProjectSyntax.encode id
  (Source.SetLanguage.mapsTo (5 : Fin (m+8)) (7 : Fin (m+8)) (6 : Fin (m+8)))) (.conj
  (ConstructionMergerCopies.copies n.succ.succ.succ.succ.succ.succ.succ.succ
  D.succ.succ.succ.succ.succ.succ.succ.succ mul.succ.succ.succ.succ.succ.succ.succ.succ
  P.succ.succ.succ.succ.succ.succ.succ.succ (7 : Fin (m+8)) (6 : Fin (m+8))) (.conj
  (ConstructionMergerCopies.projectionGraph n.succ.succ.succ.succ.succ.succ.succ.succ
  D.succ.succ.succ.succ.succ.succ.succ.succ mul.succ.succ.succ.succ.succ.succ.succ.succ
  P.succ.succ.succ.succ.succ.succ.succ.succ (7 : Fin (m+8)) (5 : Fin (m+8))) (.conj
  (ConstructionMergerCopies.equalityLaw n.succ.succ.succ.succ.succ.succ.succ.succ
  D.succ.succ.succ.succ.succ.succ.succ.succ mul.succ.succ.succ.succ.succ.succ.succ.succ
  P.succ.succ.succ.succ.succ.succ.succ.succ (5 : Fin (m+8))) (.conj
  (ConstructionProbeLetters.representatives (6 : Fin (m+8)) D.succ.succ.succ.succ.succ.succ.succ.succ (4 :
  Fin (m+8))) (.conj (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (3 : Fin (m+8)) (4 : Fin (m+8)) (6
  : Fin (m+8)))) (.conj (ConstructionMergerAction.actionTable D.succ.succ.succ.succ.succ.succ.succ.succ
  mul.succ.succ.succ.succ.succ.succ.succ.succ (5 : Fin (m+8)) (3 : Fin (m+8))) (.conj
  (ConstructionMergerAction.rightFreeAction mul.succ.succ.succ.succ.succ.succ.succ.succ
  e.succ.succ.succ.succ.succ.succ.succ.succ (6 : Fin (m+8)) (3 : Fin (m+8))) (.conj
  (ConstructionMergerAction.copyLaw D.succ.succ.succ.succ.succ.succ.succ.succ
  mul.succ.succ.succ.succ.succ.succ.succ.succ (5 : Fin (m+8)) (3 : Fin (m+8))) (.conj
  (ConstructionProbeRaw.carrier w.succ.succ.succ.succ.succ.succ.succ.succ
  D.succ.succ.succ.succ.succ.succ.succ.succ (6 : Fin (m+8)) W.succ.succ.succ.succ.succ.succ.succ.succ)
  (.conj (ConstructionProbeLetters.representatives W.succ.succ.succ.succ.succ.succ.succ.succ
  D.succ.succ.succ.succ.succ.succ.succ.succ (2 : Fin (m+8))) (.conj (ProjectSyntax.encode id
  (Source.SetLanguage.mapsTo (1 : Fin (m+8)) (2 : Fin (m+8)) W.succ.succ.succ.succ.succ.succ.succ.succ))
  (.conj (ConstructionMergerWordAction.actionTable w.succ.succ.succ.succ.succ.succ.succ.succ
  D.succ.succ.succ.succ.succ.succ.succ.succ (6 : Fin (m+8)) zero.succ.succ.succ.succ.succ.succ.succ.succ
  mul.succ.succ.succ.succ.succ.succ.succ.succ (3 : Fin (m+8)) (1 : Fin (m+8))) (.conj
  (ConstructionMergerAction.rightFreeAction mul.succ.succ.succ.succ.succ.succ.succ.succ
  e.succ.succ.succ.succ.succ.succ.succ.succ W.succ.succ.succ.succ.succ.succ.succ.succ (1 : Fin (m+8)))
  (.conj (ConstructionProbeLetters.representatives W.succ.succ.succ.succ.succ.succ.succ.succ
  W.succ.succ.succ.succ.succ.succ.succ.succ (0 : Fin (m+8))) (.conj (ProjectSyntax.encode id
  (Source.SetLanguage.mapsTo G.succ.succ.succ.succ.succ.succ.succ.succ (0 : Fin (m+8))
  W.succ.succ.succ.succ.succ.succ.succ.succ)) (.conj (ConstructionMergerWordProduct.laws
  w.succ.succ.succ.succ.succ.succ.succ.succ D.succ.succ.succ.succ.succ.succ.succ.succ (6 : Fin (m+8))
  zero.succ.succ.succ.succ.succ.succ.succ.succ (1 : Fin (m+8)) G.succ.succ.succ.succ.succ.succ.succ.succ)
  (.conj (ConstructionProbeRaw.old zero.succ.succ.succ.succ.succ.succ.succ.succ
  D.succ.succ.succ.succ.succ.succ.succ.succ e.succ.succ.succ.succ.succ.succ.succ.succ
  unit.succ.succ.succ.succ.succ.succ.succ.succ) (.conj (ConstructionProbeOldEmbeddingSyntax.oldGraph
  zero.succ.succ.succ.succ.succ.succ.succ.succ D.succ.succ.succ.succ.succ.succ.succ.succ
  O.succ.succ.succ.succ.succ.succ.succ.succ) (.conj (ConstructionMergerRoots.rootGraph
  w.succ.succ.succ.succ.succ.succ.succ.succ D.succ.succ.succ.succ.succ.succ.succ.succ (6 : Fin (m+8))
  e.succ.succ.succ.succ.succ.succ.succ.succ (5 : Fin (m+8)) unit.succ.succ.succ.succ.succ.succ.succ.succ
  roots.succ.succ.succ.succ.succ.succ.succ.succ) (ConstructionMergerRoots.rootLaws
  w.succ.succ.succ.succ.succ.succ.succ.succ D.succ.succ.succ.succ.succ.succ.succ.succ (6 : Fin (m+8))
  n.succ.succ.succ.succ.succ.succ.succ.succ mul.succ.succ.succ.succ.succ.succ.succ.succ
  P.succ.succ.succ.succ.succ.succ.succ.succ (5 : Fin (m+8)) unit.succ.succ.succ.succ.succ.succ.succ.succ
  G.succ.succ.succ.succ.succ.succ.succ.succ O.succ.succ.succ.succ.succ.succ.succ.succ
  roots.succ.succ.succ.succ.succ.succ.succ.succ))))))))))))))))))))))))))))))))

theorem merger_freeClosed {m : Nat} (w n D mul e zero P W G unit O roots : Fin m) :
    (merger w n D mul e zero P W G unit O roots).FreeClosed := by
  simp -implicitDefEqProofs [merger,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,ConstructionMergerRelations.prescription_freeClosed,ConstructionMergerRelations.valid_freeClosed,ConstructionProbeLetters.representatives_freeClosed,ConstructionMergerCopies.copies_freeClosed,ConstructionMergerCopies.projectionGraph_freeClosed,ConstructionMergerCopies.equalityLaw_freeClosed,ConstructionMergerAction.actionTable_freeClosed,ConstructionMergerAction.rightFreeAction_freeClosed,ConstructionMergerAction.copyLaw_freeClosed,ConstructionProbeRaw.carrier_freeClosed,ConstructionMergerWordAction.actionTable_freeClosed,ConstructionMergerWordProduct.laws_freeClosed,ConstructionProbeRaw.old_freeClosed,ConstructionProbeOldEmbeddingSyntax.oldGraph_freeClosed,ConstructionMergerRoots.rootGraph_freeClosed,ConstructionMergerRoots.rootLaws_freeClosed]

theorem merger_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w n D mul e zero P W G unit O roots : Fin m) :
    Project.Formula.satisfies env (merger w n D mul e zero P W G unit O roots) ↔ Merger (env.bound w) (env.bound n) (env.bound D) (env.bound mul) (env.bound e) (env.bound zero) (env.bound P) (env.bound W) (env.bound G) (env.bound unit) (env.bound O) (env.bound roots) := by
  simp only [merger,Merger,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff,
    
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ConstructionMergerRelations.prescription_semantics hM,ConstructionMergerRelations.valid_semantics hM,ConstructionProbeLetters.representatives_semantics hM,ConstructionMergerCopies.copies_semantics hM,ConstructionMergerCopies.projectionGraph_semantics hM,ConstructionMergerCopies.equalityLaw_semantics hM,ConstructionMergerAction.actionTable_semantics hM,ConstructionMergerAction.rightFreeAction_semantics hM,ConstructionMergerAction.copyLaw_semantics hM,ConstructionProbeRaw.carrier_semantics hM,ConstructionMergerWordAction.actionTable_semantics hM,ConstructionMergerWordProduct.laws_semantics hM,ConstructionProbeRaw.old_semantics hM,ConstructionProbeOldEmbeddingSyntax.oldGraph_semantics hM,ConstructionMergerRoots.rootGraph_semantics hM,ConstructionMergerRoots.rootLaws_semantics hM,ForcingSupportSize.mapsTo_semantics (M := M)]
  rfl

end PPAC.Migration.ConstructionOperationSource
