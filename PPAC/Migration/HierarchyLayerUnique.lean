import PPAC.Migration.HierarchyLayerExistence

/-! 不同实际后继域和图给出的α层值一致；层存在与唯一均为对象推导。 -/
namespace PPAC.Migration.HierarchyLayerUnique
open Source SourceAlgebra SourceLogic GraphSyntax OrdinalSyntax OrdinalRecursionSyntax HierarchyLayerSyntax

theorem deterministic_at {m} {Γ : Context m}
    (hh : Derives Γ (ObjectPowerUnion.deterministicSentence.rename Fin.elim0)) :
    Derives Γ (OrdinalRecursionDeterminism.deterministic PowerUnionSyntax.matrix Fin.elim0) := by
  simpa only [ObjectPowerUnion.deterministicSentence, OrdinalRecursionDeterminism.deterministic_rename, empty_parameters] using hh

theorem data_values_unique {m} {Γ : Context m} (hA : OrdinalRecursionContext.Evidence Γ) (a y z s f t g : Fin m)
    (hd : Derives Γ (OrdinalRecursionDeterminism.deterministic PowerUnionSyntax.matrix Fin.elim0))
    (ha : Derives Γ (ordinal a)) (hy : Derives Γ (data s f a y)) (hz : Derives Γ (data t g a z)) :
    Derives Γ (.equal y z) := by
  have hS := OrdinalSuccessor.ordinal s a hA.foundation (.conjL hy) ha
  have hT := OrdinalSuccessor.ordinal t a hA.foundation (.conjL hz) ha
  have hcomp := OrdinalRecursionCompatibility.compatible PowerUnionSyntax.matrix Fin.elim0 f g s t
    hA.extensionality hA.foundation hA.agreementSeparation hd hS hT (.conjL (.conjR hy)) (.conjL (.conjR hz))
  exact .impE (.impE (GraphFamilySyntax.agrees_at f g a y z hcomp) (.conjR (.conjR hy))) (.conjR (.conjR hz))

theorem value_against_data {m} {Γ : Context m} (hA : OrdinalRecursionContext.Evidence Γ) (a y z s f : Fin m)
    (hd : Derives Γ (OrdinalRecursionDeterminism.deterministic PowerUnionSyntax.matrix Fin.elim0))
    (ha : Derives Γ (ordinal a)) (hy : Derives Γ (data s f a y)) (hz : Derives Γ (layer a z)) : Derives Γ (.equal y z) := by
  let W := witnesses a z
  let Ξ := Context.add W (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply eliminate_layer a z _ hz
  have hAW := OrdinalRecursionContext.under_two hA W
  have hdW : Derives Ξ (OrdinalRecursionDeterminism.deterministic PowerUnionSyntax.matrix Fin.elim0) := by
    simpa only [Formula.raise, OrdinalRecursionDeterminism.deterministic_rename, empty_parameters] using OrderedPairElimination.under_two hd W
  have haW : Derives Ξ (ordinal a.castSucc.castSucc) := by
    simpa only [Formula.raise, ordinal_rename] using OrderedPairElimination.under_two ha W
  have hyW : Derives Ξ (data s.castSucc.castSucc f.castSucc.castSucc a.castSucc.castSucc y.castSucc.castSucc) := by
    simpa only [Formula.raise, data_rename] using OrderedPairElimination.under_two hy W
  have hW : Derives Ξ W := .hyp (Or.inl rfl)
  exact data_values_unique hAW a.castSucc.castSucc y.castSucc.castSucc z.castSucc.castSucc
    s.castSucc.castSucc f.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) hdW haW hyW hW

theorem layers_unique {m} {Γ : Context m} (hA : OrdinalRecursionContext.Evidence Γ) (a y z : Fin m)
    (hd : Derives Γ (OrdinalRecursionDeterminism.deterministic PowerUnionSyntax.matrix Fin.elim0))
    (ha : Derives Γ (ordinal a)) (hy : Derives Γ (layer a y)) (hz : Derives Γ (layer a z)) : Derives Γ (.equal y z) := by
  let W := witnesses a y
  let Ξ := Context.add W (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply eliminate_layer a y _ hy
  have hAW := OrdinalRecursionContext.under_two hA W
  have hdW : Derives Ξ (OrdinalRecursionDeterminism.deterministic PowerUnionSyntax.matrix Fin.elim0) := by
    simpa only [Formula.raise, OrdinalRecursionDeterminism.deterministic_rename, empty_parameters] using OrderedPairElimination.under_two hd W
  have haW : Derives Ξ (ordinal a.castSucc.castSucc) := by
    simpa only [Formula.raise, ordinal_rename] using OrderedPairElimination.under_two ha W
  have hzW : Derives Ξ (layer a.castSucc.castSucc z.castSucc.castSucc) := by
    simpa only [Formula.raise, layer_rename] using OrderedPairElimination.under_two hz W
  have hW : Derives Ξ W := .hyp (Or.inl rfl)
  exact value_against_data hAW a.castSucc.castSucc y.castSucc.castSucc z.castSucc.castSucc
    (Fin.last m).castSucc (Fin.last (m+1)) hdW haW hW hzW

theorem unique_formula {m} {Γ : Context m} (hA : OrdinalRecursionContext.Evidence Γ) (a y : Fin m)
    (hd : Derives Γ (OrdinalRecursionDeterminism.deterministic PowerUnionSyntax.matrix Fin.elim0))
    (ha : Derives Γ (ordinal a)) (hy : Derives Γ (layer a y)) : Derives Γ (uniqueLayer a y) := by
  apply Derives.allI
  let Δ := Context.image Formula.raise Γ
  have hA' := OrdinalRecursionContext.rename hA Fin.castSucc
  have hd' : Derives Δ (OrdinalRecursionDeterminism.deterministic PowerUnionSyntax.matrix Fin.elim0) := by
    simpa only [Formula.raise, OrdinalRecursionDeterminism.deterministic_rename, empty_parameters] using Derives.rename Fin.castSucc hd
  have ha' : Derives Δ (ordinal a.castSucc) := by
    simpa only [Formula.raise, ordinal_rename] using Derives.rename Fin.castSucc ha
  have hy' : Derives Δ (layer a.castSucc y.castSucc) := by
    simpa only [Formula.raise, layer_rename] using Derives.rename Fin.castSucc hy
  apply Derives.impI
  let M := layer a.castSucc (Fin.last m)
  exact layers_unique (OrdinalRecursionContext.add hA' M) a.castSucc (Fin.last m) y.castSucc
    (add hd' M) (add ha' M) (.hyp (Or.inl rfl)) (add hy' M)

theorem fiber_of_exists {m} {Γ : Context m} (hA : OrdinalRecursionContext.Evidence Γ) (a : Fin m)
    (hd : Derives Γ (OrdinalRecursionDeterminism.deterministic PowerUnionSyntax.matrix Fin.elim0))
    (ha : Derives Γ (ordinal a)) (hx : Derives Γ (layerExists a)) : Derives Γ (layerFiber a) := by
  let Y := layer a.castSucc (Fin.last m)
  let Ξ := Context.add Y (Context.image Formula.raise Γ)
  change Derives Γ (.ex Y) at hx
  apply Derives.exE (p := Y) hx
  have hAY := OrdinalRecursionContext.under hA Y
  have hdY : Derives Ξ (OrdinalRecursionDeterminism.deterministic PowerUnionSyntax.matrix Fin.elim0) := by
    simpa only [Formula.raise, OrdinalRecursionDeterminism.deterministic_rename, empty_parameters] using under hd Y
  have haY : Derives Ξ (ordinal a.castSucc) := by
    simpa only [Formula.raise, ordinal_rename] using under ha Y
  have hY : Derives Ξ Y := .hyp (Or.inl rfl)
  have huniq := unique_formula hAY a.castSucc (Fin.last m) hdY haY hY
  have hout : Derives Ξ (layerFiber a.castSucc) := by
    apply Derives.exI (Fin.last m)
    simp only [Formula.instantiate, Formula.rename, layer_rename, uniqueLayer_rename,
      Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
    exact .conjI hY huniq
  simpa only [Formula.raise, layerFiber_rename] using hout
end PPAC.Migration.HierarchyLayerUnique
