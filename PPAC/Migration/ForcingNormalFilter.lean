/- Pinned OpenAI SupportFilter.isNormalFilter, consumed by ProductNames.system.
All four clauses are derived from the actual internal small-support family.
The final certificate constructs both the full permutation carrier and filter. -/
import PPAC.Migration.ForcingSupportIntersection

namespace PPAC.Migration.ForcingNormalFilter
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open Source (Formula)
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ForcingConditionGraphs
open ForcingLabelPermutations (Carrier carrier)
open ForcingConjugationGraph (Subgroup subgroup Graph graph)
open ForcingStabilizerTransport (NormalImage normalImage)
open ForcingSupportFilter (Filter filter)
open ForcingSupportIntersection (Intersection intersection)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def Upward (I G F : M.Carrier .set) : Prop :=
  ∀ K L, (Project.FirstOrderSemantics.reduct M).mem K F → Subgroup I G L →
    (∀ x, (Project.FirstOrderSemantics.reduct M).mem x K → (Project.FirstOrderSemantics.reduct M).mem x L) →
    (Project.FirstOrderSemantics.reduct M).mem L F

def Intersections (F : M.Carrier .set) : Prop :=
  ∀ K L H, (Project.FirstOrderSemantics.reduct M).mem K F → (Project.FirstOrderSemantics.reduct M).mem L F →
    Intersection H K L → (Project.FirstOrderSemantics.reduct M).mem H F

def Conjugations (I G F : M.Carrier .set) : Prop :=
  ∀ r i c, Permutation I r → Endomap I i → InverseGraph r i →
    Permutation G c → Graph I G r i c → NormalImage F c

def Normal (I G F : M.Carrier .set) : Prop :=
  (Project.FirstOrderSemantics.reduct M).mem G F ∧ Upward I G F ∧ Intersections F ∧ Conjugations I G F

def upward {m : Nat} (I G F : Fin m) : Formula m :=
  .all (.all ((Formula.mem (Fin.last m).castSucc F.castSucc.castSucc).imp
    ((subgroup I.castSucc.castSucc G.castSucc.castSucc (Fin.last (m+1))).imp
      ((Source.SetLanguage.subset (Fin.last m).castSucc (Fin.last (m+1))).imp
        (.mem (Fin.last (m+1)) F.castSucc.castSucc)))))

def intersections {m : Nat} (F : Fin m) : Formula m :=
  .all (.all (.all ((Formula.mem (Fin.last m).castSucc.castSucc F.castSucc.castSucc.castSucc).imp
    ((Formula.mem (Fin.last (m+1)).castSucc F.castSucc.castSucc.castSucc).imp
      ((intersection (Fin.last (m+2)) (Fin.last m).castSucc.castSucc (Fin.last (m+1)).castSucc).imp
        (.mem (Fin.last (m+2)) F.castSucc.castSucc.castSucc))))))

def conjugations {m : Nat} (I G F : Fin m) : Formula m :=
  .all (.all (.all ((permutation I.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc).imp
    ((endomap I.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc).imp
      ((inverseGraph (Fin.last m).castSucc.castSucc (Fin.last (m+1)).castSucc).imp
        ((permutation G.castSucc.castSucc.castSucc (Fin.last (m+2))).imp
          ((graph I.castSucc.castSucc.castSucc G.castSucc.castSucc.castSucc
            (Fin.last m).castSucc.castSucc (Fin.last (m+1)).castSucc (Fin.last (m+2))).imp
              (normalImage F.castSucc.castSucc.castSucc (Fin.last (m+2))))))))))

def normal {m : Nat} (I G F : Fin m) : Formula m :=
  (Formula.mem G F).conj ((upward I G F).conj ((intersections F).conj (conjugations I G F)))

theorem upward_semantics {m : Nat} (env : Fin m → M.Carrier .set) (I G F : Fin m) :
    Formula.Realize (Project.FirstOrderSemantics.reduct M).mem env (upward I G F) ↔ Upward (env I) (env G) (env F) := by
  simp only [upward,Upward,Formula.Realize,ForcingConjugationGraph.subgroup_semantics (M := M),
    ForcingLabelPermutations.subset_semantics (M := M),Fin.lastCases_last,Fin.lastCases_castSucc]
  rfl

theorem intersections_semantics {m : Nat} (env : Fin m → M.Carrier .set) (F : Fin m) :
    Formula.Realize (Project.FirstOrderSemantics.reduct M).mem env (intersections F) ↔ Intersections (env F) := by
  simp only [intersections,Intersections,Formula.Realize,ForcingSupportIntersection.intersection_semantics (M := M),
    Fin.lastCases_last,Fin.lastCases_castSucc]
  rfl

theorem conjugations_semantics {m : Nat} (env : Fin m → M.Carrier .set) (I G F : Fin m) :
    Formula.Realize (Project.FirstOrderSemantics.reduct M).mem env (conjugations I G F) ↔ Conjugations (env I) (env G) (env F) := by
  simp only [conjugations,Conjugations,Formula.Realize,permutation_semantics (M := M),endomap_semantics (M := M),
    inverseGraph_semantics (M := M),ForcingConjugationGraph.graph_semantics (M := M),
    ForcingStabilizerTransport.normalImage_semantics (M := M),Fin.lastCases_last,Fin.lastCases_castSucc]
  rfl

theorem normal_semantics {m : Nat} (env : Fin m → M.Carrier .set) (I G F : Fin m) :
    Formula.Realize (Project.FirstOrderSemantics.reduct M).mem env (normal I G F) ↔ Normal (env I) (env G) (env F) := by
  simp only [normal,Normal,Formula.Realize,upward_semantics (M := M),intersections_semantics (M := M),
    conjugations_semantics (M := M)]

theorem is_normal (hM : FirstOrder.Theory.Models M nativeZF) {I G w mu F : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hmu : (Project.FirstOrderSemantics.reduct M).IsInfiniteCardinal (KuratowskiZF.interpretation hM) w mu)
    (hG : Carrier I G) (hF : Filter I G mu F) : Normal I G F := by
  refine ⟨(hF G).mpr (ForcingSupportFilter.top_supported hM hG mu),?_,?_,?_⟩
  · intro K L hK hL hKL
    exact (hF L).mpr (ForcingSupportFilter.upward_supported ((hF K).mp hK) hL hKL)
  · exact fun _ _ _ hK hL hH => ForcingSupportIntersection.intersection_mem hM hw hmu hG hF hK hL hH
  · exact fun _ _ _ hr hi hri hc hcg => ForcingSupportFilter.normal_image hM hG hF hr hi hri hc hcg

theorem exists_normal (hM : FirstOrder.Theory.Models M nativeZF) (I : M.Carrier .set) {w mu : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hmu : (Project.FirstOrderSemantics.reduct M).IsInfiniteCardinal (KuratowskiZF.interpretation hM) w mu) :
    ∃ G F, Carrier I G ∧ Filter I G mu F ∧ Normal I G F := by
  obtain ⟨G,hG⟩ := ForcingLabelPermutations.exists_carrier hM I
  obtain ⟨F,hF⟩ := ForcingSupportFilter.exists_filter hM I G mu
  exact ⟨G,F,hG,hF,is_normal hM hw hmu hG hF⟩

/-- Open parameters: omega, the infinite cardinal bound, the label set. -/
def conclusion : Formula 3 := .ex (.ex
  ((carrier (2 : Fin 3).castSucc.castSucc (Fin.last 3).castSucc).conj
    ((filter (2 : Fin 3).castSucc.castSucc (Fin.last 3).castSucc (1 : Fin 3).castSucc.castSucc (Fin.last 4)).conj
      (normal (2 : Fin 3).castSucc.castSucc (Fin.last 3).castSucc (Fin.last 4)))))

def constructionSentence : Project.Sentence where
  formula := Project.Formula.forallClosure 3 (.imp (Project.Formula.isOmega (.bound 0))
    (.imp (Project.Formula.isInfiniteCardinal PureKuratowskiProject.convention (.bound 0) (.bound 1))
      (ProjectSyntax.encode id conclusion)))
  freeClosed := by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed]

theorem construction_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence constructionSentence).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) constructionSentence]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_isOmega_iff,
    Project.Formula.satisfies_isInfiniteCardinal_iff (KuratowskiZF.interpretation hM) (ModelTransfer.extensionality hM),
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),Project.Term.eval_bound]
  intro hw hmu
  simp only [conclusion,Formula.Realize,ForcingLabelPermutations.carrier_semantics (M := M),
    ForcingSupportFilter.filter_semantics (M := M),normal_semantics (M := M),Fin.lastCases_last,Fin.lastCases_castSucc]
  exact exists_normal hM (bound 2) hw hmu

theorem construction_kernel_certificate : FirstOrder.Derives nativeZF []
    (Project.fo_sentence constructionSentence) := ModelTransfer.derives (fun _ hM => construction_models hM)

end PPAC.Migration.ForcingNormalFilter
