/- Pinned ForcingNames.lean:494-532, mapConditions_unionName / smul_union.
The source proof uses condition-order invariance and the inverse action only
to obtain preimages in P. The existing internal permutation graph supplies
exactly these preimages. No action law or union law is assumed as a field. -/
import PPAC.Migration.ForcingUnionName

namespace PPAC.Migration.ForcingUnionAction
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open Source (Formula)
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open ForcingMapConditions (MapRel IsFunction Mapped mapping)
open ForcingUnionName (UnionName Entry)
attribute [local implicit_reducible] SetTheory.signature Definitional.Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 4096
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def preservesOrder {n : Nat} (R : Formula (n+2)) (P r : Fin n) : Formula n :=
  let rho : Fin n → Fin (n+4) := fun i => i.castSucc.castSucc.castSucc.castSucc
  let x := (Fin.last n).castSucc.castSucc.castSucc
  let y := (Fin.last (n+1)).castSucc.castSucc
  let a := (Fin.last (n+2)).castSucc
  let b := Fin.last (n+3)
  .all (.all (.all (.all ((ForcingConditionAction.act (rho P) (rho r) x a).imp
    ((ForcingConditionAction.act (rho P) (rho r) y b).imp
      ((ReplacementPredicates.rel R rho a b).iff (ReplacementPredicates.rel R rho x y)))))))

def PreservesOrder {n : Nat} (R : Formula (n+2)) (params : Fin n → M.Carrier .set)
    (P r : M.Carrier .set) : Prop :=
  ∀ x y a b, ForcingConditionAction.Act P r x a → ForcingConditionAction.Act P r y b →
    (MapRel R params a b ↔ MapRel R params x y)

theorem preservesOrder_semantics {n : Nat} (v : Fin n → M.Carrier .set) (R : Formula (n+2)) (P r : Fin n) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem v (preservesOrder R P r) ↔
      PreservesOrder R v (v P) (v r) := by
  simp only [preservesOrder, Source.Formula.iff, Formula.Realize, ForcingConditionAction.act_semantics (M := M),
    ForcingMapConditions.rel_semantics (M := M), Fin.lastCases_last, Fin.lastCases_castSucc, PreservesOrder]
  constructor
  · intro h x y a b hx hy
    exact ⟨(h x y a b hx hy).1, (h x y a b hx hy).2⟩
  · intro h x y a b hx hy
    exact ⟨(h x y a b hx hy).mp, (h x y a b hx hy).mpr⟩

/-- Source's two membership directions, reusing both exact edge equations. -/
theorem map_unionName_restricted (hM : FirstOrder.Theory.Models M nativeZF) {k n : Nat}
    {f : Formula (k+2)} {R : Formula (n+2)} {fparams : Fin k → M.Carrier .set}
    {params : Fin n → M.Carrier .set} (hf : IsFunction f fparams)
    (P : M.Carrier .set) (Q : M.Carrier .set → Prop)
    (hqQ : ∀ q, (Definitional.Project.FirstOrderSemantics.reduct M).mem q P → Q q)
    (hinto : ∀ x y, (Definitional.Project.FirstOrderSemantics.reduct M).mem x P → MapRel f fparams x y →
      (Definitional.Project.FirstOrderSemantics.reduct M).mem y P)
    (honto : ∀ y, (Definitional.Project.FirstOrderSemantics.reduct M).mem y P →
      ∃ x, (Definitional.Project.FirstOrderSemantics.reduct M).mem x P ∧ MapRel f fparams x y)
    (hR : ∀ x y a b, Q x → Q y → MapRel f fparams x a → MapRel f fparams y b → (MapRel R params a b ↔ MapRel R params x y))
    {sigma name mapped output : M.Carrier .set} (hn : UnionName R params P sigma name)
    (hs : Mapped f fparams sigma mapped) (ho : Mapped f fparams name output)
    (hQ : ∀ chi p child r, PureKuratowski.PairMember M chi p sigma →
      PureKuratowski.PairMember M child r chi → Q p ∧ Q r) :
    UnionName R params P mapped output := by
  intro z
  constructor
  · intro hz
    obtain ⟨child, q, child', q', he, hchild, hqMap, hCode⟩ := (ForcingMapConditions.mem_mapping hM hf ho z).mp hz
    obtain ⟨chi, p, r, hp, hr, hq, hqp, hqr⟩ := (ForcingUnionName.edge_unionName hM hn child q).mp he
    obtain ⟨chi', hchi⟩ := ForcingMapConditions.exists_mapping hM f fparams hf chi
    obtain ⟨p', hpMap, _⟩ := hf p
    obtain ⟨r', hrMap, _⟩ := hf r
    exact ⟨child', q', hCode, chi', p', r',
      (ForcingMapConditions.edge_mapping hM hf hs chi' p').mpr ⟨chi, p, hp, hchi, hpMap⟩,
      (ForcingMapConditions.edge_mapping hM hf hchi child' r').mpr ⟨child, r, hr, hchild, hrMap⟩,
      hinto q q' hq hqMap, (hR q p q' p' (hqQ q hq) (hQ chi p child r hp hr).1 hqMap hpMap).mpr hqp, (hR q r q' r' (hqQ q hq) (hQ chi p child r hp hr).2 hqMap hrMap).mpr hqr⟩
  · rintro ⟨child, q, hCode, chi, p, r, hp, hr, hq, hqp, hqr⟩
    obtain ⟨chi', p', hp', hchi, hpMap⟩ := (ForcingMapConditions.edge_mapping hM hf hs chi p).mp hp
    obtain ⟨child', r', hr', hchild, hrMap⟩ := (ForcingMapConditions.edge_mapping hM hf hchi child r).mp hr
    obtain ⟨q', hq', hqMap⟩ := honto q hq
    apply (ForcingMapConditions.mem_mapping hM hf ho z).mpr
    exact ⟨child', q', child, q,
      (ForcingUnionName.edge_unionName hM hn child' q').mpr ⟨chi', p', r', hp', hr', hq',
        (hR q' p' q p (hqQ q' hq') (hQ chi' p' child' r' hp' hr').1 hqMap hpMap).mp hqp, (hR q' r' q r (hqQ q' hq') (hQ chi' p' child' r' hp' hr').2 hqMap hrMap).mp hqr⟩,
      hchild, hqMap, hCode⟩

/-- Original unrestricted API, retained as an instance of the shared proof. -/
theorem map_unionName (hM : FirstOrder.Theory.Models M nativeZF) {n : Nat}
    {f R : Formula (n+2)} {params : Fin n → M.Carrier .set} (hf : IsFunction f params)
    (P : M.Carrier .set)
    (hinto : ∀ x y, (Definitional.Project.FirstOrderSemantics.reduct M).mem x P → MapRel f params x y →
      (Definitional.Project.FirstOrderSemantics.reduct M).mem y P)
    (honto : ∀ y, (Definitional.Project.FirstOrderSemantics.reduct M).mem y P →
      ∃ x, (Definitional.Project.FirstOrderSemantics.reduct M).mem x P ∧ MapRel f params x y)
    (hR : ∀ x y a b, MapRel f params x a → MapRel f params y b → (MapRel R params a b ↔ MapRel R params x y))
    {sigma name mapped output : M.Carrier .set} (hn : UnionName R params P sigma name)
    (hs : Mapped f params sigma mapped) (ho : Mapped f params name output) :
    UnionName R params P mapped output := by
  exact map_unionName_restricted hM hf P (fun _ => True) (fun _ _ => True.intro)
    hinto honto (fun x y a b _ _ => hR x y a b) hn hs ho (fun _ _ _ _ _ _ => ⟨True.intro, True.intro⟩)

/-- Actual source actCode, not an assumed abstract action on names. -/
theorem action_unionName (hM : FirstOrder.Theory.Models M nativeZF) {n : Nat}
    (R : Formula (n+2)) (params : Fin n → M.Carrier .set) (P r : Fin n)
    (hr : ForcingConditionGraphs.Permutation (params P) (params r))
    (hR : PreservesOrder R params (params P) (params r))
    {sigma name mapped output : M.Carrier .set} (hn : UnionName R params (params P) sigma name)
    (hs : Mapped (ForcingConditionAction.actFormula P r) params sigma mapped)
    (ho : Mapped (ForcingConditionAction.actFormula P r) params name output) :
    UnionName R params (params P) mapped output := by
  apply map_unionName hM (ForcingConditionAction.act_function params P r hr.1) (params P) ?_ ?_ ?_ hn hs ho
  · intro x y hx hxy
    exact ForcingConditionAction.act_into hr.1 hx ((ForcingConditionAction.relation_semantics params P r x y).mp hxy)
  · intro y hy
    obtain ⟨x, hx, he⟩ := hr.2.2 y hy
    exact ⟨x, hx, (ForcingConditionAction.relation_semantics params P r x y).mpr (Or.inl ⟨hx, he⟩)⟩
  · intro x y a b hx hy
    exact hR x y a b ((ForcingConditionAction.relation_semantics params P r x a).mp hx)
      ((ForcingConditionAction.relation_semantics params P r y b).mp hy)

def actionSentence {n : Nat} (R : Formula (n+2)) (P r sigma name mapped output : Fin n) : Source.Sentence :=
  ((ForcingConditionGraphs.permutation P r).imp ((preservesOrder R P r).imp
    ((ForcingUnionName.unionName R id P sigma name).imp
      ((mapping (ForcingConditionAction.actFormula P r) id sigma mapped).imp
        ((mapping (ForcingConditionAction.actFormula P r) id name output).imp
          (ForcingUnionName.unionName R id P mapped output)))))).close

theorem action_models {n : Nat} (R : Formula (n+2)) (P r sigma name mapped output : Fin n)
    (hM : FirstOrder.Theory.Models M nativeZF) :
    (Translation.sentence (actionSentence R P r sigma name mapped output)).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro v hr hR hn hs ho
  exact (ForcingUnionName.unionName_semantics (M := M) v R id P mapped output).mpr
    (action_unionName hM R v P r ((ForcingConditionGraphs.permutation_semantics (M := M) v P r).mp hr)
      ((preservesOrder_semantics (M := M) v R P r).mp hR)
      ((ForcingUnionName.unionName_semantics (M := M) v R id P sigma name).mp hn)
      ((ForcingMapConditions.mapping_semantics (M := M) v (ForcingConditionAction.actFormula P r) id sigma mapped).mp hs)
      ((ForcingMapConditions.mapping_semantics (M := M) v (ForcingConditionAction.actFormula P r) id name output).mp ho))

theorem action_kernel_certificate {n : Nat} (R : Formula (n+2)) (P r sigma name mapped output : Fin n) :
    FirstOrder.Derives nativeZF [] (Translation.sentence (actionSentence R P r sigma name mapped output)) :=
  ModelTransfer.derives (fun _ hM => action_models R P r sigma name mapped output hM)

/-- Equality form of original smul_union, using the already proved unique range. -/
theorem action_equal (hM : FirstOrder.Theory.Models M nativeZF) {n : Nat}
    (R : Formula (n+2)) (params : Fin n → M.Carrier .set) (P r : Fin n)
    (hr : ForcingConditionGraphs.Permutation (params P) (params r))
    (hR : PreservesOrder R params (params P) (params r))
    {sigma name mapped output target : M.Carrier .set} (hn : UnionName R params (params P) sigma name)
    (hs : Mapped (ForcingConditionAction.actFormula P r) params sigma mapped)
    (ho : Mapped (ForcingConditionAction.actFormula P r) params name output)
    (ht : UnionName R params (params P) mapped target) : output = target :=
  ForcingUnionName.unique hM (action_unionName hM R params P r hr hR hn hs ho) ht

def equalitySentence {n : Nat} (R : Formula (n+2)) (P r sigma name mapped output target : Fin n) : Source.Sentence :=
  ((ForcingConditionGraphs.permutation P r).imp ((preservesOrder R P r).imp
    ((ForcingUnionName.unionName R id P sigma name).imp
      ((mapping (ForcingConditionAction.actFormula P r) id sigma mapped).imp
        ((mapping (ForcingConditionAction.actFormula P r) id name output).imp
          ((ForcingUnionName.unionName R id P mapped target).imp (.equal output target))))))).close

theorem equality_models {n : Nat} (R : Formula (n+2)) (P r sigma name mapped output target : Fin n)
    (hM : FirstOrder.Theory.Models M nativeZF) :
    (Translation.sentence (equalitySentence R P r sigma name mapped output target)).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro v hr hR hn hs ho ht
  exact action_equal hM R v P r ((ForcingConditionGraphs.permutation_semantics (M := M) v P r).mp hr)
    ((preservesOrder_semantics (M := M) v R P r).mp hR)
    ((ForcingUnionName.unionName_semantics (M := M) v R id P sigma name).mp hn)
    ((ForcingMapConditions.mapping_semantics (M := M) v (ForcingConditionAction.actFormula P r) id sigma mapped).mp hs)
    ((ForcingMapConditions.mapping_semantics (M := M) v (ForcingConditionAction.actFormula P r) id name output).mp ho)
    ((ForcingUnionName.unionName_semantics (M := M) v R id P mapped target).mp ht)

theorem equality_kernel_certificate {n : Nat} (R : Formula (n+2)) (P r sigma name mapped output target : Fin n) :
    FirstOrder.Derives nativeZF [] (Translation.sentence (equalitySentence R P r sigma name mapped output target)) :=
  ModelTransfer.derives (fun _ hM => equality_models R P r sigma name mapped output target hM)

end PPAC.Migration.ForcingUnionAction
