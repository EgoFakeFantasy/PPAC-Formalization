/- Pinned CohenForcing.Condition.permute: image of the whole partial-function
graph under coordinatePerm. Reuse native PowerSet/Separation, the existing
exact-image constructor and small_image. The general bound w specializes
to internal omega; the value carrier specializes to internal 2. -/
import PPAC.Migration.ForcingCohenCoordinates

namespace PPAC.Migration.ForcingCohenConditions
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open Source (Formula)
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open ForcingConditionGraphs
open ForcingCohenCoordinates (Graph graph)
open ForcingSupportSize (Small small)
open ForcingStabilizerTransport (Image image)
attribute [local implicit_reducible] SetTheory.signature Definitional.Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def Functional (p : M.Carrier .set) : Prop :=
  ∀ x y z, PureKuratowski.PairMember M x y p → PureKuratowski.PairMember M x z p → y = z

def functional {m : Nat} (p : Fin m) : Formula m :=
  .all (.all (.all ((Source.SetLanguage.edge p.castSucc.castSucc.castSucc
    (Fin.last m).castSucc.castSucc (Fin.last (m+1)).castSucc).imp
      ((Source.SetLanguage.edge p.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc
        (Fin.last (m+2))).imp (.equal (Fin.last (m+1)).castSucc (Fin.last (m+2)))))))

theorem functional_semantics {m : Nat} (env : Fin m → M.Carrier .set) (p : Fin m) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem env (functional p) ↔ Functional (env p) := by
  simp only [functional, Functional, Formula.Realize, KuratowskiZF.source_edge,
    Fin.lastCases_last, Fin.lastCases_castSucc]
  rfl

def Condition (S w p : M.Carrier .set) : Prop :=
  (∀ z, (Definitional.Project.FirstOrderSemantics.reduct M).mem z p →
    (Definitional.Project.FirstOrderSemantics.reduct M).mem z S) ∧ Functional p ∧ Small p w

def condition {m : Nat} (S w p : Fin m) : Formula m :=
  (Source.SetLanguage.subset p S).conj ((functional p).conj (small p w))

theorem condition_semantics {m : Nat} (env : Fin m → M.Carrier .set) (S w p : Fin m) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem env (condition S w p) ↔
      Condition (env S) (env w) (env p) := by
  simp only [condition, Condition, Formula.Realize, ForcingLabelPermutations.subset_semantics (M := M),
    functional_semantics (M := M), ForcingSupportSize.small_semantics (M := M)]

def Carrier (S w X : M.Carrier .set) : Prop :=
  ∀ p, (Definitional.Project.FirstOrderSemantics.reduct M).mem p X ↔ Condition S w p

def carrier {m : Nat} (S w X : Fin m) : Formula m :=
  .all ((Formula.mem (Fin.last m) X.castSucc).iff (condition S.castSucc w.castSucc (Fin.last m)))

theorem carrier_semantics {m : Nat} (env : Fin m → M.Carrier .set) (S w X : Fin m) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem env (carrier S w X) ↔
      Carrier (env S) (env w) (env X) := by
  simp only [carrier, Carrier, Source.Formula.iff, Formula.Realize, condition_semantics (M := M),
    Fin.lastCases_last, Fin.lastCases_castSucc]
  exact ⟨fun h p => ⟨(h p).1, (h p).2⟩, fun h p => ⟨(h p).mp, (h p).mpr⟩⟩

theorem exists_carrier (hM : FirstOrder.Theory.Models M nativeZF) (S w : M.Carrier .set) :
    ∃ X, Carrier S w X := by
  obtain ⟨power, hPower⟩ := SetTheory.ZF.exists_powerSet (ModelTransfer.project_models_iff.mp hM) S
  let params := Source.SetLanguage.args2 S w
  let query := condition (0 : Fin 2).castSucc (1 : Fin 2).castSucc (Fin.last 2)
  have sep := (GodelDefOutput.separation_semantics (Definitional.Project.FirstOrderSemantics.reduct M).mem query).mp
    ((Translation.realizes_sentence M _).mp ((SeparationSyntax.source_separation query).semantically_entails M hM))
  obtain ⟨X, hX⟩ := sep params power
  have hq : ∀ p, Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem
      (Fin.lastCases p params) query ↔ Condition S w p := by
    intro p
    exact condition_semantics (M := M) (Fin.lastCases p params) (0 : Fin 2).castSucc (1 : Fin 2).castSucc (Fin.last 2)
  refine ⟨X, fun p => ?_⟩
  exact ⟨fun hp => (hq p).mp ((hX p).mp hp).2,
    fun hp => (hX p).mpr ⟨(hPower p).mpr hp.1, (hq p).mpr hp⟩⟩

/-- Exact edge formula of the source image operation, keeping the output bit. -/
theorem image_edge (hM : FirstOrder.Theory.Models M nativeZF) {S f g p q : M.Carrier .set}
    (hg : Graph S f g) (hp : ∀ z, (Definitional.Project.FirstOrderSemantics.reduct M).mem z p →
      (Definitional.Project.FirstOrderSemantics.reduct M).mem z S) (him : Image g p q) (a b : M.Carrier .set) :
    PureKuratowski.PairMember M a b q ↔
      ∃ x, PureKuratowski.PairMember M x a f ∧ PureKuratowski.PairMember M x b p := by
  constructor
  · rintro ⟨z, hz, hzq⟩
    obtain ⟨t, htp, htz⟩ := (him z).mp hzq
    obtain ⟨_, x, y, v, ht, hxv, hz'⟩ := (hg t z).mp htz
    obtain ⟨rfl, rfl⟩ := PureKuratowski.code_injective hz' hz
    exact ⟨x, hxv, t, ht, htp⟩
  · rintro ⟨x, hxa, t, ht, htp⟩
    obtain ⟨z, hz⟩ := KuratowskiZF.exists_code hM a b
    exact ⟨z, hz, (him z).mpr ⟨t, htp, (hg t z).mpr ⟨hp t htp, x, b, a, ht, hxa, hz⟩⟩⟩

theorem condition_image (hM : FirstOrder.Theory.Models M nativeZF) {C S w f g p q : M.Carrier .set}
    (hf : Permutation C f) (hg : Permutation S g) (hgraph : Graph S f g)
    (hp : Condition S w p) (him : Image g p q) : Condition S w q := by
  refine ⟨?_, ?_, ForcingSupportSize.small_image hM hg him hp.2.2⟩
  · intro z hz
    obtain ⟨t, _, htz⟩ := (him z).mp hz
    exact hg.1.2 t z htz
  · intro a b c hab hac
    obtain ⟨x, hxa, hxb⟩ := (image_edge hM hgraph hp.1 him a b).mp hab
    obtain ⟨y, hya, hyc⟩ := (image_edge hM hgraph hp.1 him a c).mp hac
    have hxy := hf.2.1 x y a hxa hya
    exact hp.2.1 x b c hxb (hxy ▸ hyc)

theorem exists_permute (hM : FirstOrder.Theory.Models M nativeZF) {C S w f g p : M.Carrier .set}
    (hf : Permutation C f) (hg : Permutation S g) (hgraph : Graph S f g) (hp : Condition S w p) :
    ∃ q, Image g p q ∧ Condition S w q := by
  obtain ⟨q, him, _⟩ := ForcingLabelConjugacy.exists_image hM hg.1 (J := p)
  exact ⟨q, him, condition_image hM hf hg hgraph hp him⟩

/-- Source image_subset_image_iff; reversed inclusion is Cohen's forcing order. -/
theorem image_subset_iff {S g p q P Q : M.Carrier .set} (hg : Permutation S g)
    (hp : ∀ x, (Definitional.Project.FirstOrderSemantics.reduct M).mem x p →
      (Definitional.Project.FirstOrderSemantics.reduct M).mem x S)
    (hP : Image g p P) (hQ : Image g q Q) :
    (∀ y, (Definitional.Project.FirstOrderSemantics.reduct M).mem y P →
      (Definitional.Project.FirstOrderSemantics.reduct M).mem y Q) ↔
    (∀ x, (Definitional.Project.FirstOrderSemantics.reduct M).mem x p →
      (Definitional.Project.FirstOrderSemantics.reduct M).mem x q) := by
  constructor
  · intro h x hx
    obtain ⟨y, hxy, _⟩ := hg.1.1.2 x (hp x hx)
    obtain ⟨z, hz, hzy⟩ := (hQ y).mp (h y ((hP y).mpr ⟨x, hx, hxy⟩))
    exact hg.2.1 z x y hzy hxy ▸ hz
  · intro h y hy
    obtain ⟨x, hx, hxy⟩ := (hP y).mp hy
    exact (hQ y).mpr ⟨x, h x hx, hxy⟩

def carrierSentence : Source.Sentence :=
  (Formula.ex (carrier (0 : Fin 2).castSucc (1 : Fin 2).castSucc (Fin.last 2))).close

def preservationSentence : Source.Sentence :=
  ((permutation (0 : Fin 7) 3).imp ((permutation 1 4).imp ((graph 1 3 4).imp
    ((condition 1 2 5).imp ((image 4 5 6).imp (condition 1 2 6)))))).close

def constructionSentence : Source.Sentence :=
  ((permutation (0 : Fin 6) 3).imp ((permutation 1 4).imp ((graph 1 3 4).imp
    ((condition 1 2 5).imp (.ex ((image (4 : Fin 6).castSucc (5 : Fin 6).castSucc (Fin.last 6)).conj
      (condition (1 : Fin 6).castSucc (2 : Fin 6).castSucc (Fin.last 6)))))))).close

def orderSentence : Source.Sentence :=
  ((permutation (0 : Fin 6) 1).imp ((Source.SetLanguage.subset 2 0).imp ((image 1 2 4).imp
    ((image 1 3 5).imp ((Source.SetLanguage.subset 4 5).iff (Source.SetLanguage.subset 2 3)))))).close

theorem carrier_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Translation.sentence carrierSentence).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro env
  obtain ⟨X, hX⟩ := exists_carrier hM (env 0) (env 1)
  refine ⟨X, ?_⟩
  apply (carrier_semantics (M := M) (Fin.lastCases X env) (0 : Fin 2).castSucc (1 : Fin 2).castSucc (Fin.last 2)).mpr
  simpa only [Fin.lastCases_last, Fin.lastCases_castSucc] using hX

theorem preservation_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Translation.sentence preservationSentence).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro env hf hg hgraph hp him
  apply (condition_semantics (M := M) env 1 2 6).mpr
  exact condition_image hM ((permutation_semantics (M := M) env 0 3).mp hf)
    ((permutation_semantics (M := M) env 1 4).mp hg) ((ForcingCohenCoordinates.graph_semantics (M := M) env 1 3 4).mp hgraph)
    ((condition_semantics (M := M) env 1 2 5).mp hp) ((ForcingStabilizerTransport.image_semantics (M := M) env 4 5 6).mp him)

theorem construction_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Translation.sentence constructionSentence).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro env hf hg hgraph hp
  obtain ⟨q, him, hq⟩ := exists_permute hM ((permutation_semantics (M := M) env 0 3).mp hf)
    ((permutation_semantics (M := M) env 1 4).mp hg) ((ForcingCohenCoordinates.graph_semantics (M := M) env 1 3 4).mp hgraph)
    ((condition_semantics (M := M) env 1 2 5).mp hp)
  refine ⟨q, ?_, ?_⟩
  · apply (ForcingStabilizerTransport.image_semantics (M := M) (Fin.lastCases q env)
      (4 : Fin 6).castSucc (5 : Fin 6).castSucc (Fin.last 6)).mpr
    simpa only [Fin.lastCases_last, Fin.lastCases_castSucc] using him
  · apply (condition_semantics (M := M) (Fin.lastCases q env) (1 : Fin 6).castSucc
      (2 : Fin 6).castSucc (Fin.last 6)).mpr
    simpa only [Fin.lastCases_last, Fin.lastCases_castSucc] using hq

theorem order_models (_hM : FirstOrder.Theory.Models M nativeZF) :
    (Translation.sentence orderSentence).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro env hg hp hP hQ
  have h := image_subset_iff ((permutation_semantics (M := M) env 0 1).mp hg)
    ((ForcingLabelPermutations.subset_semantics (M := M) env 2 0).mp hp)
    ((ForcingStabilizerTransport.image_semantics (M := M) env 1 2 4).mp hP)
    ((ForcingStabilizerTransport.image_semantics (M := M) env 1 3 5).mp hQ)
  have h' := (ForcingLabelPermutations.subset_semantics (M := M) env 4 5).trans
    (h.trans (ForcingLabelPermutations.subset_semantics (M := M) env 2 3).symm)
  exact ⟨h'.mp, h'.mpr⟩

theorem carrier_kernel_certificate : FirstOrder.Derives nativeZF [] (Translation.sentence carrierSentence) :=
  ModelTransfer.derives (fun _ hM => carrier_models hM)
theorem preservation_kernel_certificate : FirstOrder.Derives nativeZF [] (Translation.sentence preservationSentence) :=
  ModelTransfer.derives (fun _ hM => preservation_models hM)
theorem construction_kernel_certificate : FirstOrder.Derives nativeZF [] (Translation.sentence constructionSentence) :=
  ModelTransfer.derives (fun _ hM => construction_models hM)
theorem order_kernel_certificate : FirstOrder.Derives nativeZF [] (Translation.sentence orderSentence) :=
  ModelTransfer.derives (fun _ hM => order_models hM)

end PPAC.Migration.ForcingCohenConditions
