import PPAC.Migration.Internal.StructuralListSyntax

/-! 实际零/单位见证的构造、唯一性和对象消去，不引入宿主数值常量。 -/
namespace PPAC.Migration.Internal.StructuralListUnits
open Source SourceAlgebra SourceLogic OmegaSyntax StructuralListSyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem member {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w z e : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z)) (he : Derives Γ (successor e z)) : Derives Γ (.mem e w) :=
  OmegaStructureAlgebra.successor_member w e z (ZFContext.arithmetic hZ).base.extensionality hw
    (OmegaStructureAlgebra.zero_member w z (ZFContext.arithmetic hZ).base.extensionality hw hz) he

theorem unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (z e s f : Fin m)
    (hz : Derives Γ (empty z)) (he : Derives Γ (successor e z)) (hs : Derives Γ (empty s)) (hf : Derives Γ (successor f s)) :
    Derives Γ (.equal e f) := by
  have hzs := OmegaUniversal.empty_unique z s (ZFContext.arithmetic hZ).base.extensionality hz hs
  exact OmegaUniversal.successor_unique e f s (ZFContext.arithmetic hZ).base.extensionality
    (GodelUnpairArithmetic.successor_base_subst _ _ _ hzs he) hf

theorem exists_units {m} {Γ : Context m} (w : Fin m) (hw : Derives Γ (omega w)) : Derives Γ (units m) := by
  let Z := (Formula.mem (Fin.last m) w.castSucc).conj (empty (Fin.last m))
  let Ξ := Context.add Z (Context.image Formula.raise Γ)
  have hz : Derives Γ (.ex Z) := .conjL (.conjL hw)
  apply Derives.exE (p := Z) hz
  have hw1 : Derives Ξ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw Z
  have hZ : Derives Ξ Z := .hyp (Or.inl rfl)
  have he := Derives.impE (step_at w.castSucc (Fin.last m) (.conjL hw1)) (.conjL hZ)
  let E := (Formula.mem (Fin.last (m+1)) w.castSucc.castSucc).conj (successor (Fin.last (m+1)) (Fin.last m).castSucc)
  let Δ := Context.add E (Context.image Formula.raise Ξ)
  change Derives Ξ (.ex E) at he
  apply Derives.exE (p := E) he
  have hZ2 : Derives Δ ((Formula.mem (Fin.last m).castSucc w.castSucc.castSucc).conj (empty (Fin.last m).castSucc)) := by
    simpa only [Z, Formula.raise, Formula.rename, empty_rename] using under hZ E
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have hout : Derives Δ (units (m+2)) := by
    apply Derives.exI (Fin.last m).castSucc
    apply Derives.exI (Fin.last (m+1))
    simp only [unitWitness, Formula.instantiate, Formula.rename, empty_rename, successor_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
    exact .conjI (.conjR hZ2) (.conjR hE)
  simpa only [units, unitWitness, Formula.raise, Formula.rename, empty_rename, successor_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc] using hout

theorem with_units {m} {Γ : Context m} (w : Fin m) (r : Formula m) (hw : Derives Γ (omega w))
    (hc : Derives (Context.add (unitWitness m) (Context.image Formula.raise (Context.image Formula.raise Γ))) r.raise.raise) : Derives Γ r := by
  have hu := exists_units w hw
  change Derives Γ (.ex (.ex _)) at hu
  apply Derives.exE hu
  apply Derives.exE (.hyp (Or.inl rfl))
  refine Derives.weaken ?_ hc
  rintro r (hr | ⟨s, hs, he⟩)
  · exact Or.inl hr
  · exact Or.inr ⟨s, Or.inr hs, he⟩

theorem payload_subst {m} {Γ : Context m} (w e q p n : Fin m) (he : Derives Γ (.equal q p))
    (hn : Derives Γ (StructuralNodeSyntax.raw w e q n)) : Derives Γ (StructuralNodeSyntax.raw w e p n) := by
  have hi : Derives Γ ((StructuralNodeSyntax.raw w.castSucc e.castSucc (Fin.last m) n.castSucc).instantiate q) := by
    simpa only [Formula.instantiate, StructuralNodeSyntax.raw_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hn
  have ho := Derives.eqSubst (StructuralNodeSyntax.raw w.castSucc e.castSucc (Fin.last m) n.castSucc) he hi
  simpa only [Formula.instantiate, StructuralNodeSyntax.raw_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using ho
end PPAC.Migration.Internal.StructuralListUnits
