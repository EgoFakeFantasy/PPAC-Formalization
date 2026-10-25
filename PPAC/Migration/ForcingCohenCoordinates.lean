/- Pinned CohenForcing.Condition.coordinatePerm = (pi.prodCongr id).prodCongr id.
Use actual internal products and the native definable-function constructor.
The native product-injection wrapper forgets coordinate equations, so retain
them here for the source functional/countable-graph and order consumers. -/
import PPAC.Migration.ForcingSupportSize
import YesMetaZFC.SetTheory.ProductConstruction

namespace PPAC.Migration.ForcingCohenCoordinates
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open Source (Formula)
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open ForcingConditionGraphs
attribute [local implicit_reducible] SetTheory.signature Definitional.Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def Cartesian (A B S : M.Carrier .set) : Prop :=
  ∀ z, (Definitional.Project.FirstOrderSemantics.reduct M).mem z S ↔ ∃ x,
    (Definitional.Project.FirstOrderSemantics.reduct M).mem x A ∧ ∃ y,
      (Definitional.Project.FirstOrderSemantics.reduct M).mem y B ∧ PureKuratowski.Code M z x y

def cartesian {m : Nat} (A B S : Fin m) : Formula m :=
  .all ((Formula.mem (Fin.last m) S.castSucc).iff (.ex
    ((Formula.mem (Fin.last (m+1)) A.castSucc.castSucc).conj (.ex
      ((Formula.mem (Fin.last (m+2)) B.castSucc.castSucc.castSucc).conj
        (PairSyntax.ordered (Fin.last m).castSucc.castSucc (Fin.last (m+1)).castSucc (Fin.last (m+2))))))))

theorem cartesian_semantics {m : Nat} (env : Fin m → M.Carrier .set) (A B S : Fin m) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem env (cartesian A B S) ↔
      Cartesian (env A) (env B) (env S) := by
  simp only [cartesian, Cartesian, Source.Formula.iff, Formula.Realize, KuratowskiZF.source_code,
    Fin.lastCases_last, Fin.lastCases_castSucc]
  exact ⟨fun h z => ⟨(h z).1, (h z).2⟩, fun h z => ⟨(h z).mp, (h z).mpr⟩⟩

theorem exists_cartesian (hM : FirstOrder.Theory.Models M nativeZF) (A B : M.Carrier .set) :
    ∃ S, Cartesian A B S :=
  SetTheory.ZF.exists_cartesianProduct (ModelTransfer.project_models_iff.mp hM) (KuratowskiZF.interpretation hM) A B

/-- pi on the left coordinate and the identity on the right. -/
def Lifted (pi z w : M.Carrier .set) : Prop :=
  ∃ x y v, PureKuratowski.Code M z x y ∧ PureKuratowski.PairMember M x v pi ∧ PureKuratowski.Code M w v y

def lifted {m : Nat} (pi z w : Fin m) : Formula m :=
  .ex (.ex (.ex ((PairSyntax.ordered z.castSucc.castSucc.castSucc
    (Fin.last m).castSucc.castSucc (Fin.last (m+1)).castSucc).conj
      ((Source.SetLanguage.edge pi.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc (Fin.last (m+2))).conj
        (PairSyntax.ordered w.castSucc.castSucc.castSucc (Fin.last (m+2)) (Fin.last (m+1)).castSucc)))))

theorem lifted_semantics {m : Nat} (env : Fin m → M.Carrier .set) (pi z w : Fin m) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem env (lifted pi z w) ↔
      Lifted (env pi) (env z) (env w) := by
  simp only [lifted, Lifted, Formula.Realize, KuratowskiZF.source_code, KuratowskiZF.source_edge,
    Fin.lastCases_last, Fin.lastCases_castSucc]
  rfl

def Graph (S pi f : M.Carrier .set) : Prop :=
  ∀ z w, PureKuratowski.PairMember M z w f ↔
    (Definitional.Project.FirstOrderSemantics.reduct M).mem z S ∧ Lifted pi z w

def graph {m : Nat} (S pi f : Fin m) : Formula m :=
  .all (.all ((Source.SetLanguage.edge f.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))).iff
    ((Formula.mem (Fin.last m).castSucc S.castSucc.castSucc).conj
      (lifted pi.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))))))

theorem graph_semantics {m : Nat} (env : Fin m → M.Carrier .set) (S pi f : Fin m) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem env (graph S pi f) ↔
      Graph (env S) (env pi) (env f) := by
  simp only [graph, Graph, Source.Formula.iff, Formula.Realize, KuratowskiZF.source_edge,
    lifted_semantics (M := M), Fin.lastCases_last, Fin.lastCases_castSucc]
  exact ⟨fun h z w => ⟨(h z w).1, (h z w).2⟩, fun h z w => ⟨(h z w).mp, (h z w).mpr⟩⟩

theorem lifted_unique (hM : FirstOrder.Theory.Models M nativeZF) {A pi z w t : M.Carrier .set}
    (hp : Endomap A pi) (hw : Lifted pi z w) (ht : Lifted pi z t) : w = t := by
  obtain ⟨x, y, v, hz, hxv, hw⟩ := hw
  obtain ⟨a, b, c, hz', hac, ht⟩ := ht
  obtain ⟨rfl, rfl⟩ := PureKuratowski.code_injective hz hz'
  have he := function_unique hp.1 hxv hac
  exact KuratowskiZF.code_unique hM hw (he ▸ ht)

theorem exists_lift (hM : FirstOrder.Theory.Models M nativeZF) {A B S pi : M.Carrier .set}
    (hS : Cartesian A B S) (hp : Permutation A pi) : ∃ f, Permutation S f ∧ Graph S pi f := by
  let params : Fin 1 → M.Carrier .set := fun _ => pi
  let query := lifted (0 : Fin 1).castSucc.castSucc (Fin.last 1).castSucc (Fin.last 2)
  let env : SetTheory.Env (Definitional.Project.FirstOrderSemantics.reduct M) 1 :=
    { bound := fun j => params j.rev, free := fun _ => S }
  have hRel : ∀ z w, (ProjectSyntax.binary query).denote env z w ↔ Lifted pi z w := by
    intro z w
    rw [ForcingMapConditions.binary_semantics hM query params S z w]
    simp only [ForcingMapConditions.MapRel, query, lifted_semantics (M := M), params,
      Fin.lastCases_last, Fin.lastCases_castSucc]
  obtain ⟨f, hf, he⟩ := SetTheory.ZF.exists_setFunctionFromTo_of_denote
    (ModelTransfer.project_models_iff.mp hM) (KuratowskiZF.interpretation hM) (ProjectSyntax.binary query) env
    (source := S) (target := S)
    (fun z hz => by
      obtain ⟨x, hx, y, _, hz⟩ := (hS z).mp hz
      obtain ⟨v, hxv, _⟩ := hp.1.1.2 x hx
      obtain ⟨w, hw⟩ := KuratowskiZF.exists_code hM v y
      exact ⟨w, (hRel z w).mpr ⟨x, y, v, hz, hxv, hw⟩⟩)
    (fun z _ w t hw ht => lifted_unique hM hp.1 ((hRel z w).mp hw) ((hRel z t).mp ht))
    (fun z w hz hw => by
      obtain ⟨x, _, y, hy, hz⟩ := (hS z).mp hz
      obtain ⟨a, b, v, hz', hav, hw⟩ := (hRel z w).mp hw
      obtain ⟨rfl, rfl⟩ := PureKuratowski.code_injective hz hz'
      exact (hS w).mpr ⟨v, hp.1.2 x v hav, y, hy, hw⟩)
  have hg : Graph S pi f := fun z w => (he z w).trans (and_congr Iff.rfl (hRel z w))
  refine ⟨f, ⟨(native_endomap hM S f).mpr hf, ?_, ?_⟩, hg⟩
  · intro z t w hzw htw
    obtain ⟨_, x, y, v, hz, hxv, hw⟩ := (hg z w).mp hzw
    obtain ⟨_, a, b, c, ht, hac, hw'⟩ := (hg t w).mp htw
    obtain ⟨rfl, rfl⟩ := PureKuratowski.code_injective hw hw'
    have hxa := hp.2.1 x a v hxv hac
    exact KuratowskiZF.code_unique hM hz (hxa ▸ ht)
  · intro w hw
    obtain ⟨v, hv, y, hy, hw⟩ := (hS w).mp hw
    obtain ⟨x, hx, hxv⟩ := hp.2.2 v hv
    obtain ⟨z, hz⟩ := KuratowskiZF.exists_code hM x y
    have hzS := (hS z).mpr ⟨x, hx, y, hy, hz⟩
    exact ⟨z, hzS, (hg z w).mpr ⟨hzS, x, y, v, hz, hxv, hw⟩⟩

/-- The coordinate lift of the inverse is the literal inverse graph. -/
theorem inverse_graph {S pi inv f g : M.Carrier .set}
    (hf : Endomap S f) (hg : Endomap S g) (hi : InverseGraph pi inv)
    (hfg : Graph S pi f) (hgg : Graph S inv g) : InverseGraph f g := by
  intro z w
  constructor
  · intro hzw
    obtain ⟨_, x, y, v, hz, hxv, hw⟩ := (hfg z w).mp hzw
    exact (hgg w z).mpr ⟨hf.2 z w hzw, v, y, x, hw, (hi x v).mp hxv, hz⟩
  · intro hwz
    obtain ⟨_, v, y, x, hw, hvx, hz⟩ := (hgg w z).mp hwz
    exact (hfg z w).mpr ⟨hg.2 w z hwz, x, y, v, hz, (hi x v).mpr hvx, hw⟩

/-- Both lifts in the original coordinatePerm, for arbitrary level and value sets. -/
theorem exists_coordinates (hM : FirstOrder.Theory.Models M nativeZF) (I K B : M.Carrier .set)
    {pi : M.Carrier .set} (hp : Permutation I pi) :
    ∃ C S f g, Cartesian I K C ∧ Cartesian C B S ∧
      Permutation C f ∧ Graph C pi f ∧ Permutation S g ∧ Graph S f g := by
  obtain ⟨C, hC⟩ := exists_cartesian hM I K
  obtain ⟨S, hS⟩ := exists_cartesian hM C B
  obtain ⟨f, hf, hfg⟩ := exists_lift hM hC hp
  obtain ⟨g, hg, hgg⟩ := exists_lift hM hS hf
  exact ⟨C, S, f, g, hC, hS, hf, hfg, hg, hgg⟩

def constructionSentence : Source.Sentence :=
  ((permutation (0 : Fin 4) 3).imp (.ex (.ex (.ex (.ex ((cartesian (0 : Fin 4).castSucc.castSucc.castSucc.castSucc (1 : Fin 4).castSucc.castSucc.castSucc.castSucc (Fin.last 4).castSucc.castSucc.castSucc).conj
      ((cartesian (Fin.last 4).castSucc.castSucc.castSucc (2 : Fin 4).castSucc.castSucc.castSucc.castSucc (Fin.last 5).castSucc.castSucc).conj
      ((permutation (Fin.last 4).castSucc.castSucc.castSucc (Fin.last 6).castSucc).conj
      ((graph (Fin.last 4).castSucc.castSucc.castSucc (3 : Fin 4).castSucc.castSucc.castSucc.castSucc (Fin.last 6).castSucc).conj
      ((permutation (Fin.last 5).castSucc.castSucc (Fin.last 7)).conj
      (graph (Fin.last 5).castSucc.castSucc (Fin.last 6).castSucc (Fin.last 7)))))))))))).close

theorem construction_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Translation.sentence constructionSentence).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro env hp
  obtain ⟨C, S, f, g, hC, hS, hf, hfg, hg, hgg⟩ := exists_coordinates hM (env 0) (env 1) (env 2)
    ((permutation_semantics (M := M) env 0 3).mp hp)
  let v : Fin 8 → M.Carrier .set := Fin.lastCases g (Fin.lastCases f (Fin.lastCases S (Fin.lastCases C env)))
  refine ⟨C, S, f, g, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply (cartesian_semantics (M := M) v (0 : Fin 4).castSucc.castSucc.castSucc.castSucc
      (1 : Fin 4).castSucc.castSucc.castSucc.castSucc (Fin.last 4).castSucc.castSucc.castSucc).mpr
    simpa only [v, Fin.lastCases_last, Fin.lastCases_castSucc] using hC
  · apply (cartesian_semantics (M := M) v (Fin.last 4).castSucc.castSucc.castSucc
      (2 : Fin 4).castSucc.castSucc.castSucc.castSucc (Fin.last 5).castSucc.castSucc).mpr
    simpa only [v, Fin.lastCases_last, Fin.lastCases_castSucc] using hS
  · apply (permutation_semantics (M := M) v (Fin.last 4).castSucc.castSucc.castSucc (Fin.last 6).castSucc).mpr
    simpa only [v, Fin.lastCases_last, Fin.lastCases_castSucc] using hf
  · apply (graph_semantics (M := M) v (Fin.last 4).castSucc.castSucc.castSucc
      (3 : Fin 4).castSucc.castSucc.castSucc.castSucc (Fin.last 6).castSucc).mpr
    simpa only [v, Fin.lastCases_last, Fin.lastCases_castSucc] using hfg
  · apply (permutation_semantics (M := M) v (Fin.last 5).castSucc.castSucc (Fin.last 7)).mpr
    simpa only [v, Fin.lastCases_last, Fin.lastCases_castSucc] using hg
  · apply (graph_semantics (M := M) v (Fin.last 5).castSucc.castSucc (Fin.last 6).castSucc (Fin.last 7)).mpr
    simpa only [v, Fin.lastCases_last, Fin.lastCases_castSucc] using hgg

theorem construction_kernel_certificate :
    FirstOrder.Derives nativeZF [] (Translation.sentence constructionSentence) :=
  ModelTransfer.derives (fun _ hM => construction_models hM)

end PPAC.Migration.ForcingCohenCoordinates
