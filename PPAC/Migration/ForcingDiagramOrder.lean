/- Pinned Diagrams.Diagram.sub, le_iff, permute_sub, permuteOrderIso.
The multiplication table is an internal graph of ((n,x),y), not a host
multiplication function. Translation invariance holds for every such table;
the source monoid construction later supplies its algebraic laws. No
partial-order/monoid existence is inferred from this invariant alone. -/
import PPAC.Migration.ForcingDiagramCarrier

namespace PPAC.Migration.ForcingDiagramOrder
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open Source (Formula)
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open ForcingConditionGraphs
open ForcingSupportSize (Injection)
open ForcingDiagramCarrier (Carrier Graph carrier graph)
attribute [local implicit_reducible] SetTheory.signature Definitional.Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def Product (mul n x y : M.Carrier .set) : Prop :=
  ∃ p, PureKuratowski.Code M p n x ∧ PureKuratowski.PairMember M p y mul

def product {m : Nat} (mul n x y : Fin m) : Formula m :=
  .ex ((PairSyntax.ordered (Fin.last m) n.castSucc x.castSucc).conj
    (Source.SetLanguage.edge mul.castSucc (Fin.last m) y.castSucc))

theorem product_semantics {m : Nat} (env : Fin m → M.Carrier .set) (mul n x y : Fin m) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem env (product mul n x y) ↔
      Product (env mul) (env n) (env x) (env y) := by
  simp only [product, Product, Formula.Realize, KuratowskiZF.source_code, KuratowskiZF.source_edge,
    Fin.lastCases_last, Fin.lastCases_castSucc]
  rfl

/-- Literal source sub r n x = r (n*x), with all values internal to D. -/
def Sub (D mul r n s : M.Carrier .set) : Prop :=
  ∀ x z, PureKuratowski.PairMember M x z s ↔
    (Definitional.Project.FirstOrderSemantics.reduct M).mem x D ∧ ∃ y,
      (Definitional.Project.FirstOrderSemantics.reduct M).mem y D ∧ Product mul n x y ∧
        PureKuratowski.PairMember M y z r

def sub {m : Nat} (D mul r n s : Fin m) : Formula m :=
  .all (.all ((Source.SetLanguage.edge s.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))).iff
    ((Formula.mem (Fin.last m).castSucc D.castSucc.castSucc).conj (.ex
      ((Formula.mem (Fin.last (m+2)) D.castSucc.castSucc.castSucc).conj
        ((product mul.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc
          (Fin.last m).castSucc.castSucc (Fin.last (m+2))).conj
          (Source.SetLanguage.edge r.castSucc.castSucc.castSucc (Fin.last (m+2)) (Fin.last (m+1)).castSucc)))))))

theorem sub_semantics {m : Nat} (env : Fin m → M.Carrier .set) (D mul r n s : Fin m) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem env (sub D mul r n s) ↔
      Sub (env D) (env mul) (env r) (env n) (env s) := by
  simp only [sub, Sub, Source.Formula.iff, Formula.Realize, KuratowskiZF.source_edge,
    product_semantics (M := M), Fin.lastCases_last, Fin.lastCases_castSucc]
  exact ⟨fun h x z => ⟨(h x z).1, (h x z).2⟩, fun h x z => ⟨(h x z).mp, (h x z).mpr⟩⟩

def Le (D mul r s : M.Carrier .set) : Prop :=
  ∃ n, (Definitional.Project.FirstOrderSemantics.reduct M).mem n D ∧ Sub D mul r n s

def le {m : Nat} (D mul r s : Fin m) : Formula m :=
  .ex ((Formula.mem (Fin.last m) D.castSucc).conj
    (sub D.castSucc mul.castSucc r.castSucc (Fin.last m) s.castSucc))

theorem le_semantics {m : Nat} (env : Fin m → M.Carrier .set) (D mul r s : Fin m) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem env (le D mul r s) ↔
      Le (env D) (env mul) (env r) (env s) := by
  simp only [le, Le, Formula.Realize, sub_semantics (M := M), Fin.lastCases_last, Fin.lastCases_castSucc]

/-- The fixed-left multiplication contract supplied by source LeftCancelMonoid. -/
def LeftInjection (D mul n : M.Carrier .set) : Prop :=
  (∀ x, (Definitional.Project.FirstOrderSemantics.reduct M).mem x D →
    ∃ y, (Definitional.Project.FirstOrderSemantics.reduct M).mem y D ∧ Product mul n x y) ∧
  (∀ x y z, (Definitional.Project.FirstOrderSemantics.reduct M).mem x D →
    Product mul n x y → Product mul n x z → y = z) ∧
  (∀ x y z, (Definitional.Project.FirstOrderSemantics.reduct M).mem x D →
    (Definitional.Project.FirstOrderSemantics.reduct M).mem y D →
    Product mul n x z → Product mul n y z → x = y)

def leftInjection {m : Nat} (D mul n : Fin m) : Formula m :=
  let up : Fin m → Fin (m+3) := fun i => i.castSucc.castSucc.castSucc
  let x := (Fin.last m).castSucc.castSucc
  let y := (Fin.last (m+1)).castSucc
  let z := Fin.last (m+2)
  (Formula.all ((Formula.mem (Fin.last m) D.castSucc).imp (.ex
    ((Formula.mem (Fin.last (m+1)) D.castSucc.castSucc).conj
      (product mul.castSucc.castSucc n.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))))))).conj
  ((Formula.all (Formula.all (Formula.all ((Formula.mem x (up D)).imp ((product (up mul) (up n) x y).imp
    ((product (up mul) (up n) x z).imp (.equal y z))))))).conj
  (Formula.all (Formula.all (Formula.all ((Formula.mem x (up D)).imp ((Formula.mem y (up D)).imp
    ((product (up mul) (up n) x z).imp ((product (up mul) (up n) y z).imp (.equal x y)))))))))

theorem leftInjection_semantics {m : Nat} (env : Fin m → M.Carrier .set) (D mul n : Fin m) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem env (leftInjection D mul n) ↔
      LeftInjection (env D) (env mul) (env n) := by
  simp only [leftInjection, LeftInjection, Formula.Realize, product_semantics (M := M),
    Fin.lastCases_last, Fin.lastCases_castSucc]
  rfl

/-- Construct source sub from actual multiplication entries, using the donor twice. -/
theorem exists_sub (hM : FirstOrder.Theory.Models M nativeZF) {D I mul n r : M.Carrier .set}
    (hleft : LeftInjection D mul n) (hr : Injection D I r) :
    ∃ s, Injection D I s ∧ Sub D mul r n s := by
  let params := Source.SetLanguage.args2 mul n
  let query := product (0 : Fin 2).castSucc.castSucc (1 : Fin 2).castSucc.castSucc
    (Fin.last 2).castSucc (Fin.last 3)
  let env : SetTheory.Env (Definitional.Project.FirstOrderSemantics.reduct M) 2 :=
    { bound := fun j => params j.rev, free := fun _ => D }
  have hRel : ∀ x y, (ProjectSyntax.binary query).denote env x y ↔ Product mul n x y := by
    intro x y
    rw [ForcingMapConditions.binary_semantics hM query params D x y]
    simp only [ForcingMapConditions.MapRel, query, product_semantics (M := M), params,
      Fin.lastCases_last, Fin.lastCases_castSucc]
    rfl
  obtain ⟨f, hf, he⟩ := SetTheory.ZF.exists_setFunctionFromTo_of_denote
    (ModelTransfer.project_models_iff.mp hM) (KuratowskiZF.interpretation hM) (ProjectSyntax.binary query) env
    (source := D) (target := D)
    (fun x hx => by obtain ⟨y, _, hy⟩ := hleft.1 x hx; exact ⟨y, (hRel x y).mpr hy⟩)
    (fun x hx y z hy hz => hleft.2.1 x y z hx ((hRel x y).mp hy) ((hRel x z).mp hz))
    (fun x y hx hy => by
      obtain ⟨z, hz, hpz⟩ := hleft.1 x hx
      exact hleft.2.1 x z y hx hpz ((hRel x y).mp hy) ▸ hz)
  have hfedge : ∀ x y, PureKuratowski.PairMember M x y f ↔
      (Definitional.Project.FirstOrderSemantics.reduct M).mem x D ∧ Product mul n x y :=
    fun x y => (he x y).trans (and_congr Iff.rfl (hRel x y))
  obtain ⟨s, hs, hcomp⟩ := SetTheory.ZF.exists_compositionFunction
    (ModelTransfer.project_models_iff.mp hM) (KuratowskiZF.interpretation hM) hf
    ((ForcingSupportSize.native_mapsTo hM D I r).mp hr.1)
  refine ⟨s, ⟨(ForcingSupportSize.native_mapsTo hM D I s).mpr hs, ?_⟩, ?_⟩
  · intro x y z hx hy
    obtain ⟨hxD, a, hxa, haz⟩ := (hcomp x z).mp hx
    obtain ⟨hyD, b, hyb, hbz⟩ := (hcomp y z).mp hy
    have hab := hr.2 a b z haz hbz
    exact hleft.2.2 x y a hxD hyD ((hfedge x a).mp hxa).2
      (hab ▸ ((hfedge y b).mp hyb).2)
  · intro x z
    constructor
    · intro hxz
      obtain ⟨hx, y, hxy, hyz⟩ := (hcomp x z).mp hxz
      exact ⟨hx, y, hf.output_mem_of_pairMember hxy, ((hfedge x y).mp hxy).2, hyz⟩
    · rintro ⟨hx, y, _, hxy, hyz⟩
      exact (hcomp x z).mpr ⟨hx, y, (hfedge x y).mpr ⟨hx, hxy⟩, hyz⟩

def subConstructionSentence : Source.Sentence :=
  ((leftInjection (0 : Fin 5) 2 3).imp ((Source.SetLanguage.injection 4 0 1).imp (.ex
    ((Source.SetLanguage.injection (Fin.last 5) (0 : Fin 5).castSucc (1 : Fin 5).castSucc).conj
      (sub (0 : Fin 5).castSucc (2 : Fin 5).castSucc (4 : Fin 5).castSucc (3 : Fin 5).castSucc (Fin.last 5)))))).close

theorem subConstruction_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Translation.sentence subConstructionSentence).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro env hl hr
  obtain ⟨s, hs, hsub⟩ := exists_sub hM ((leftInjection_semantics (M := M) env 0 2 3).mp hl)
    ((ForcingSupportSize.injection_semantics (M := M) env 4 0 1).mp hr)
  refine ⟨s, ?_, ?_⟩
  · apply (ForcingSupportSize.injection_semantics (M := M) (Fin.lastCases s env)
      (Fin.last 5) (0 : Fin 5).castSucc (1 : Fin 5).castSucc).mpr
    simpa only [Fin.lastCases_last, Fin.lastCases_castSucc] using hs
  · apply (sub_semantics (M := M) (Fin.lastCases s env) (0 : Fin 5).castSucc
      (2 : Fin 5).castSucc (4 : Fin 5).castSucc (3 : Fin 5).castSucc (Fin.last 5)).mpr
    simpa only [Fin.lastCases_last, Fin.lastCases_castSucc] using hsub

theorem subConstruction_kernel_certificate :
    FirstOrder.Derives nativeZF [] (Translation.sentence subConstructionSentence) :=
  ModelTransfer.derives (fun _ hM => subConstruction_models hM)

/-- Associativity of graph evaluation proves exactly source permute_sub. -/
theorem permute_sub {D mul pi r s R S n : M.Carrier .set}
    (hr : CompositionGraph D pi r R) (hs : CompositionGraph D pi s S)
    (hsub : Sub D mul r n s) : Sub D mul R n S := by
  intro x z
  constructor
  · intro hxz
    obtain ⟨hx, a, hxa, haz⟩ := (hs x z).mp hxz
    obtain ⟨_, y, hy, hprod, hya⟩ := (hsub x a).mp hxa
    exact ⟨hx, y, hy, hprod, (hr y z).mpr ⟨hy, a, hya, haz⟩⟩
  · rintro ⟨hx, y, hy, hprod, hyz⟩
    obtain ⟨_, a, hya, haz⟩ := (hr y z).mp hyz
    exact (hs x z).mpr ⟨hx, a, (hsub x a).mpr ⟨hx, y, hy, hprod, hya⟩, haz⟩

theorem sub_iff (hM : FirstOrder.Theory.Models M nativeZF) {D I mul pi r s R S n : M.Carrier .set}
    (hp : Permutation I pi) (hr : Injection D I r) (hs : Injection D I s)
    (hR : CompositionGraph D pi r R) (hS : CompositionGraph D pi s S) :
    Sub D mul r n s ↔ Sub D mul R n S := by
  obtain ⟨inv, _, hi⟩ := exists_inverse hM hp
  exact ⟨permute_sub hR hS, permute_sub (ForcingDiagramCarrier.reverse hp hr hi hR)
    (ForcingDiagramCarrier.reverse hp hs hi hS)⟩

theorem le_iff (hM : FirstOrder.Theory.Models M nativeZF) {D I mul pi r s R S : M.Carrier .set}
    (hp : Permutation I pi) (hr : Injection D I r) (hs : Injection D I s)
    (hR : CompositionGraph D pi r R) (hS : CompositionGraph D pi s S) :
    Le D mul r s ↔ Le D mul R S :=
  exists_congr (fun _ => and_congr Iff.rfl (sub_iff hM hp hr hs hR hS))

def OrderPreserving (D mul a : M.Carrier .set) : Prop :=
  ∀ r s R S, PureKuratowski.PairMember M r R a → PureKuratowski.PairMember M s S a →
    (Le D mul r s ↔ Le D mul R S)

def orderPreserving {m : Nat} (D mul a : Fin m) : Formula m :=
  let up : Fin m → Fin (m+4) := fun i => i.castSucc.castSucc.castSucc.castSucc
  let r := (Fin.last m).castSucc.castSucc.castSucc
  let s := (Fin.last (m+1)).castSucc.castSucc
  let R := (Fin.last (m+2)).castSucc
  let S := Fin.last (m+3)
  .all (.all (.all (.all ((Source.SetLanguage.edge (up a) r R).imp
    ((Source.SetLanguage.edge (up a) s S).imp ((le (up D) (up mul) r s).iff (le (up D) (up mul) R S)))))))

theorem orderPreserving_semantics {m : Nat} (env : Fin m → M.Carrier .set) (D mul a : Fin m) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem env (orderPreserving D mul a) ↔
      OrderPreserving (env D) (env mul) (env a) := by
  simp only [orderPreserving, OrderPreserving, Source.Formula.iff, Formula.Realize, KuratowskiZF.source_edge,
    le_semantics (M := M), Fin.lastCases_last, Fin.lastCases_castSucc]
  exact ⟨fun h r s R S hr hs => ⟨(h r s R S hr hs).1, (h r s R S hr hs).2⟩,
    fun h r s R S hr hs => ⟨(h r s R S hr hs).mp, (h r s R S hr hs).mpr⟩⟩

theorem graph_order (hM : FirstOrder.Theory.Models M nativeZF) {D I X mul pi a : M.Carrier .set}
    (hX : Carrier D I X) (hp : Permutation I pi) (hg : Graph D X pi a) : OrderPreserving D mul a := by
  intro r s R S hr hs
  obtain ⟨hr, _, hR⟩ := (hg r R).mp hr
  obtain ⟨hs, _, hS⟩ := (hg s S).mp hs
  exact le_iff hM hp ((hX r).mp hr) ((hX s).mp hs) hR hS

/-- Construct the whole carrier and an actual order-preserving permutation on it. -/
theorem exists_order_action (hM : FirstOrder.Theory.Models M nativeZF) (D I mul : M.Carrier .set)
    {pi : M.Carrier .set} (hp : Permutation I pi) :
    ∃ X a, Carrier D I X ∧ Permutation X a ∧ Graph D X pi a ∧ OrderPreserving D mul a := by
  obtain ⟨X, hX⟩ := ForcingDiagramCarrier.exists_carrier hM D I
  obtain ⟨a, ha, hg⟩ := ForcingDiagramCarrier.exists_graph hM hX hp
  exact ⟨X, a, hX, ha, hg, graph_order hM hX hp hg⟩

def constructionSentence : Source.Sentence :=
  ((permutation (1 : Fin 4) 3).imp (.ex (.ex
    ((carrier (0 : Fin 4).castSucc.castSucc (1 : Fin 4).castSucc.castSucc (Fin.last 4).castSucc).conj
      ((permutation (Fin.last 4).castSucc (Fin.last 5)).conj
        ((graph (0 : Fin 4).castSucc.castSucc (Fin.last 4).castSucc (3 : Fin 4).castSucc.castSucc (Fin.last 5)).conj
          (orderPreserving (0 : Fin 4).castSucc.castSucc (2 : Fin 4).castSucc.castSucc (Fin.last 5)))))))).close

theorem construction_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Translation.sentence constructionSentence).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro env hp
  obtain ⟨X, a, hX, ha, hg, ho⟩ := exists_order_action hM (env 0) (env 1) (env 2)
    ((permutation_semantics (M := M) env 1 3).mp hp)
  let v : Fin 6 → M.Carrier .set := Fin.lastCases a (Fin.lastCases X env)
  refine ⟨X, a, ?_, ?_, ?_, ?_⟩
  · apply (ForcingDiagramCarrier.carrier_semantics (M := M) v (0 : Fin 4).castSucc.castSucc
      (1 : Fin 4).castSucc.castSucc (Fin.last 4).castSucc).mpr
    simpa only [v, Fin.lastCases_last, Fin.lastCases_castSucc] using hX
  · apply (permutation_semantics (M := M) v (Fin.last 4).castSucc (Fin.last 5)).mpr
    simpa only [v, Fin.lastCases_last, Fin.lastCases_castSucc] using ha
  · apply (ForcingDiagramCarrier.graph_semantics (M := M) v (0 : Fin 4).castSucc.castSucc
      (Fin.last 4).castSucc (3 : Fin 4).castSucc.castSucc (Fin.last 5)).mpr
    simpa only [v, Fin.lastCases_last, Fin.lastCases_castSucc] using hg
  · apply (orderPreserving_semantics (M := M) v (0 : Fin 4).castSucc.castSucc
      (2 : Fin 4).castSucc.castSucc (Fin.last 5)).mpr
    simpa only [v, Fin.lastCases_last, Fin.lastCases_castSucc] using ho

theorem construction_kernel_certificate :
    FirstOrder.Derives nativeZF [] (Translation.sentence constructionSentence) :=
  ModelTransfer.derives (fun _ hM => construction_models hM)

end PPAC.Migration.ForcingDiagramOrder
