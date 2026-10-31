/- Pinned StableSelectors.Good/good_dense:137,183-219, for the concrete
regular Hartogs(omega) bit index used by ConcreteSystem.kappa.
Assemble the existing pair-separating Complete extension, actual rows and
full germ pattern. Both Complete and actual pattern injectivity hold for
the SAME extending condition. Consumer: conditionSelector/component_selector_dense. -/
import PPAC.Migration.ConstructionGermPatternInjectivity
import PPAC.Migration.ConstructionGermBoundedRows

namespace PPAC.Migration.ConstructionGermGoodDense
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ForcingSupportSize (MapsTo Injection Small)
open ForcingCohenCoordinates (Cartesian)
open ForcingCohenConditions (Condition)
open ConstructionGermEventual (Space)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def Good (w D chain H G N K C B lo hi det p : M.Carrier .set) : Prop := ∃ alpha R A S E pr T F,
  (Project.FirstOrderSemantics.reduct M).mem alpha K ∧ ConstructionCohenRows.Rows C B lo hi p R ∧
    Space alpha B A ∧ Space w A S ∧ MapsTo S E pr ∧ ConstructionGermEventual.Classes w S E ∧
      ConstructionGermEventual.Projection w S pr ∧ ConstructionGermEventual.Exact w pr ∧ Space N E T ∧
        ConstructionGermPattern.Pattern w D chain H G N alpha B A E T det R pr F ∧ Injection G T F ∧
          ConstructionGermComplete.Complete w H N det alpha p

def good {m : Nat} (w D chain H G N K C B lo hi det p : Fin m) : Project.Formula 1 m := (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.conj (.mem (.bound 7) (.bound K.succ.succ.succ.succ.succ.succ.succ.succ)) (.conj (ConstructionCohenRows.rows C.succ.succ.succ.succ.succ.succ.succ.succ B.succ.succ.succ.succ.succ.succ.succ.succ lo.succ.succ.succ.succ.succ.succ.succ.succ hi.succ.succ.succ.succ.succ.succ.succ.succ p.succ.succ.succ.succ.succ.succ.succ.succ 6) (.conj (ConstructionGermEventual.space 7 B.succ.succ.succ.succ.succ.succ.succ.succ 5) (.conj (ConstructionGermEventual.space w.succ.succ.succ.succ.succ.succ.succ.succ 5 4) (.conj (ProjectSyntax.encode id (Source.SetLanguage.mapsTo 2 4 3)) (.conj (ConstructionGermEventual.classes w.succ.succ.succ.succ.succ.succ.succ.succ 4 3) (.conj (ConstructionGermEventual.projection w.succ.succ.succ.succ.succ.succ.succ.succ 4 2) (.conj (ConstructionGermEventual.exactProjection w.succ.succ.succ.succ.succ.succ.succ.succ 2) (.conj (ConstructionGermEventual.space N.succ.succ.succ.succ.succ.succ.succ.succ 3 1) (.conj (ConstructionGermPattern.pattern w.succ.succ.succ.succ.succ.succ.succ.succ D.succ.succ.succ.succ.succ.succ.succ.succ chain.succ.succ.succ.succ.succ.succ.succ.succ H.succ.succ.succ.succ.succ.succ.succ.succ G.succ.succ.succ.succ.succ.succ.succ.succ N.succ.succ.succ.succ.succ.succ.succ.succ 7 B.succ.succ.succ.succ.succ.succ.succ.succ 5 3 1 det.succ.succ.succ.succ.succ.succ.succ.succ 6 2 0) (.conj (ProjectSyntax.encode id (Source.SetLanguage.injection 0 G.succ.succ.succ.succ.succ.succ.succ.succ 1)) (ConstructionGermComplete.complete w.succ.succ.succ.succ.succ.succ.succ.succ H.succ.succ.succ.succ.succ.succ.succ.succ N.succ.succ.succ.succ.succ.succ.succ.succ det.succ.succ.succ.succ.succ.succ.succ.succ 7 p.succ.succ.succ.succ.succ.succ.succ.succ))))))))))))))))))))

theorem good_freeClosed {m : Nat} (w D chain H G N K C B lo hi det p : Fin m) : (good w D chain H G N K C B lo hi det p).FreeClosed := by
  simp -implicitDefEqProofs [good,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
    ConstructionCohenRows.rows_freeClosed,ConstructionGermEventual.space_freeClosed,ConstructionGermEventual.classes_freeClosed,
    ConstructionGermEventual.projection_freeClosed,ConstructionGermEventual.exactProjection_freeClosed,
    ConstructionGermPattern.pattern_freeClosed,ConstructionGermComplete.complete_freeClosed]

theorem good_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w D chain H G N K C B lo hi det p : Fin m) :
    Project.Formula.satisfies env (good w D chain H G N K C B lo hi det p) ↔ Good (env.bound w) (env.bound D) (env.bound chain) (env.bound H) (env.bound G) (env.bound N) (env.bound K) (env.bound C) (env.bound B) (env.bound lo) (env.bound hi) (env.bound det) (env.bound p) := by
  simp only [good,Good,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,ConstructionCohenRows.rows_semantics hM,
    ConstructionGermEventual.space_semantics hM,ConstructionGermEventual.classes_semantics hM,
    ConstructionGermEventual.projection_semantics hM,ConstructionGermEventual.exactProjection_semantics hM,
    ConstructionGermPattern.pattern_semantics hM,ConstructionGermComplete.complete_semantics hM,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ForcingSupportSize.mapsTo_semantics (M := M),
    ForcingSupportSize.injection_semantics (M := M)]
  rfl

theorem good_dense (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M))
    {w D I mul q zero root vertices chain H G N X reps det J K C B S lo hi p : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hHartogs : ConstructionSaturationIndex.Hartogs hM w K)
    (hReg : (Project.FirstOrderSemantics.reduct M).IsRegularCardinal (KuratowskiZF.interpretation hM) K)
    (hChain : ConstructionComponentCofinal.Chain w D I mul q zero root vertices chain)
    (hH : ConstructionGermCosets.Carrier D I mul q root H) (hG : ConstructionGermCosets.Classes w D chain H G)
    (hDet : ConstructionGermDetectors.Detectors D I chain X reps det)
    (hSep : ConstructionGermSeparation.Separation w D chain H N det)
    (hX : Cartesian N w X) (hCover : ConstructionGermDetectorSites.Covers w H det J)
    (hJ : Small J w) (hJI : (Project.FirstOrderSemantics.reduct M).MemberSubset J I)
    (hC : Cartesian I K C) (hS : Cartesian C B S)
    (hlo : ForcingWithTopCarrier.Empty lo) (hhi : (Project.FirstOrderSemantics.reduct M).SuccessorOf hi lo)
    (hB : (Project.FirstOrderSemantics.reduct M).SuccessorOf B hi) (hp : Condition S w p) :
    ∃ r, Condition S w r ∧ (Project.FirstOrderSemantics.reduct M).MemberSubset p r ∧ Good w D chain H G N K C B lo hi det r := by
  have hloB := (hB lo).mpr (Or.inl hhi.predecessor_mem)
  obtain ⟨pairs,alpha,r,hPairs,_,hAlpha,_,hr,hpr,hComplete,hReq⟩ :=
    ConstructionGermBoundedRows.construction hM hChoice hw hHartogs hReg hH hDet hX hCover hJ hJI hC hS hloB hB.predecessor_mem hp
  obtain ⟨R,hRows,hExtend⟩ := ConstructionCohenRows.construction hM hlo hhi hB hS hr
  obtain ⟨A,Seq,E,pr,T,F,hA,hSeq,hProjection,hE,hProj,hExact,hT,hPattern,_⟩ :=
    ConstructionGermPattern.construction hM hw hChain hDet hH hG hX hC hRows.1 (hHartogs.1.transitive alpha hAlpha)
  have hInject := ConstructionGermPatternInjectivity.construction hM hw hSep hCover hPairs hReq hExtend hExact hPattern hlo hhi
  exact ⟨r,hr,hpr,alpha,R,A,Seq,E,pr,T,F,hAlpha,hRows,hA,hSeq,hProjection,hE,hProj,hExact,hT,hPattern,hInject,hComplete⟩

def constructionSentence {m : Nat} (w D I mul q zero root vertices chain H G N X reps det J K C B S lo hi p : Fin m) : Project.Sentence where
  formula := Project.Formula.forallClosure m (.imp (Project.Formula.isOmega (.bound w)) (.imp (ConstructionSaturationIndex.hartogs w K) (.imp (ConstructionSaturationIndex.regular K) (.imp (ConstructionComponentCofinal.chain w D I mul q zero root vertices chain) (.imp (ConstructionGermCosets.carrier D I mul q root H) (.imp (ConstructionGermCosets.classes w D chain H G) (.imp (ConstructionGermDetectors.detectors D I chain X reps det) (.imp (ConstructionGermSeparation.separation w D chain H N det) (.imp (ProjectSyntax.encode id (ForcingCohenCoordinates.cartesian N w X)) (.imp (ConstructionGermDetectorSites.coversFormula w H det J) (.imp (ProjectSyntax.encode id (ForcingSupportSize.small J w)) (.imp (Project.Formula.subset (.bound J) (.bound I)) (.imp (ProjectSyntax.encode id (ForcingCohenCoordinates.cartesian I K C)) (.imp (ProjectSyntax.encode id (ForcingCohenCoordinates.cartesian C B S)) (.imp (Project.Formula.isEmpty (.bound lo)) (.imp (Project.Formula.isSuccessor (.bound hi) (.bound lo)) (.imp (Project.Formula.isSuccessor (.bound B) (.bound hi)) (.imp (ProjectSyntax.encode id (ForcingCohenConditions.condition S w p)) (.existsE (.conj (ProjectSyntax.encode id (ForcingCohenConditions.condition S.succ w.succ 0)) (.conj (Project.Formula.subset (.bound p.succ) (.bound 0)) (good w.succ D.succ chain.succ H.succ G.succ N.succ K.succ C.succ B.succ lo.succ hi.succ det.succ 0))))))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,Project.Formula.isOmega,Project.Formula.subset,
      Project.Formula.isEmpty,Project.Formula.isSuccessor,Project.Formula.extensionalEq,ProjectSyntax.freeClosed,
      ConstructionSaturationIndex.hartogs_freeClosed,ConstructionSaturationIndex.regular_freeClosed,
      ConstructionComponentCofinal.chain_freeClosed,ConstructionGermCosets.carrier_freeClosed,ConstructionGermCosets.classes_freeClosed,
      ConstructionGermDetectors.detectors_freeClosed,ConstructionGermSeparation.separation_freeClosed,
      ConstructionGermDetectorSites.coversFormula_freeClosed,good_freeClosed]

theorem construction_models {m : Nat} (w D I mul q zero root vertices chain H G N X reps det J K C B S lo hi p : Fin m) (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) :
    (Project.fo_sentence (constructionSentence w D I mul q zero root vertices chain H G N X reps det J K C B S lo hi p)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) (constructionSentence w D I mul q zero root vertices chain H G N X reps det J K C B S lo hi p)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_isOmega_iff,Project.Formula.satisfies_subset_iff,Project.Formula.satisfies_isEmpty_iff,
    Project.Formula.satisfies_isSuccessor_iff,Project.Term.eval_bound,ConstructionSaturationIndex.hartogs_semantics hM,
    ConstructionSaturationIndex.regular_semantics hM,ConstructionComponentCofinal.chain_semantics hM,
    ConstructionGermCosets.carrier_semantics hM,ConstructionGermCosets.classes_semantics hM,
    ConstructionGermDetectors.detectors_semantics hM,ConstructionGermSeparation.separation_semantics hM,
    ConstructionGermDetectorSites.coversFormula_semantics hM,good_semantics hM,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ForcingSupportSize.small_semantics (M := M),
    ForcingCohenCoordinates.cartesian_semantics (M := M),ForcingCohenConditions.condition_semantics (M := M)]
  exact good_dense hM hChoice

theorem construction_kernel_certificate {m : Nat} (w D I mul q zero root vertices chain H G N X reps det J K C B S lo hi p : Fin m) : FirstOrder.Derives nativeZF []
    (Project.fo_sentence (ConstructibleGround.relative (constructionSentence w D I mul q zero root vertices chain H G N X reps det J K C B S lo hi p))) := by
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
  apply ConstructibleGround.relative_models hM (constructionSentence w D I mul q zero root vertices chain H G N X reps det J K C B S lo hi p)
  exact (Project.FirstOrderSemantics.sentence_correct
    (ModelTransfer.extensionality hL) (constructionSentence w D I mul q zero root vertices chain H G N X reps det J K C B S lo hi p)).mp (construction_models w D I mul q zero root vertices chain H G N X reps det J K C B S lo hi p hL hChoice)

end PPAC.Migration.ConstructionGermGoodDense
