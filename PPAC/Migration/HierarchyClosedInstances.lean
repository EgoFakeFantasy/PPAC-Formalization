import PPAC.Migration.ObjectHierarchyAlgebra
import PPAC.Migration.ObjectCumulativeHierarchy

/-! 已证层闭句在任意对象上下文的实例；每个证书参数均在最终ZF推导中消去。 -/
namespace PPAC.Migration.HierarchyClosedInstances
open Source SourceAlgebra SourceLogic OrdinalSyntax HierarchyLayerSyntax HierarchyMemberSyntax

theorem existence {m} {Γ : Context m} (a : Fin m)
    (hc : Derives Γ (ObjectCumulativeHierarchy.existenceSentence.rename Fin.elim0))
    (ha : Derives Γ (ordinal a)) : Derives Γ (layerExists a) := by
  have hi := specialize_close ((ordinal (0 : Fin 1)).imp (layerExists 0)) (fun _ => a) hc
  have h : Derives Γ ((ordinal a).imp (layerExists a)) := by
    simpa only [Formula.rename, ordinal_rename, layerExists_rename] using hi
  exact .impE h ha

theorem uniqueness {m} {Γ : Context m} (a : Fin m)
    (hc : Derives Γ (ObjectCumulativeHierarchy.uniquenessSentence.rename Fin.elim0))
    (ha : Derives Γ (ordinal a)) : Derives Γ (layerFiber a) := by
  have hi := specialize_close ((ordinal (0 : Fin 1)).imp (layerFiber 0)) (fun _ => a) hc
  have h : Derives Γ ((ordinal a).imp (layerFiber a)) := by
    simpa only [Formula.rename, ordinal_rename, layerFiber_rename] using hi
  exact .impE h ha

theorem membership {m} {Γ : Context m} (a y : Fin m)
    (hc : Derives Γ (ObjectHierarchyAlgebra.membershipSentence.rename Fin.elim0))
    (ha : Derives Γ (ordinal a)) (hy : Derives Γ (layer a y)) : Derives Γ (HierarchyMemberSyntax.membership a y) := by
  let ρ : Fin 2 → Fin m := Fin.cases a (fun _ => y)
  have h0 : ρ 0 = a := rfl
  have h1 : ρ 1 = y := rfl
  have hi := specialize_close ((ordinal (0 : Fin 2)).imp ((layer 0 1).imp (HierarchyMemberSyntax.membership 0 1))) ρ hc
  have h : Derives Γ ((ordinal a).imp ((layer a y).imp (HierarchyMemberSyntax.membership a y))) := by
    simpa only [Formula.rename, ordinal_rename, layer_rename, membership_rename, h0, h1] using hi
  exact .impE (.impE h ha) hy

theorem successor {m} {Γ : Context m} (a s u v : Fin m)
    (hc : Derives Γ (ObjectHierarchyAlgebra.successorSentence.rename Fin.elim0))
    (ha : Derives Γ (ordinal a)) (hs : Derives Γ (OmegaSyntax.successor s a))
    (hu : Derives Γ (layer a u)) (hv : Derives Γ (layer s v)) : Derives Γ (PowerSetSyntax.powerOf v u) := by
  let ρ : Fin 4 → Fin m := Fin.cases a (Fin.cases s (Fin.cases u (fun _ => v)))
  have h0 : ρ 0 = a := rfl
  have h1 : ρ 1 = s := rfl
  have h2 : ρ 2 = u := rfl
  have h3 : ρ 3 = v := rfl
  have hi := specialize_close ((ordinal (0 : Fin 4)).imp ((OmegaSyntax.successor 1 0).imp
    ((layer 0 2).imp ((layer 1 3).imp (PowerSetSyntax.powerOf 3 2))))) ρ hc
  have h : Derives Γ ((ordinal a).imp ((OmegaSyntax.successor s a).imp
      ((layer a u).imp ((layer s v).imp (PowerSetSyntax.powerOf v u))))) := by
    simpa only [Formula.rename, ordinal_rename, OmegaSyntax.successor_rename, layer_rename,
      PowerSetSyntax.powerOf_rename, h0, h1, h2, h3] using hi
  exact .impE (.impE (.impE (.impE h ha) hs) hu) hv
end PPAC.Migration.HierarchyClosedInstances
