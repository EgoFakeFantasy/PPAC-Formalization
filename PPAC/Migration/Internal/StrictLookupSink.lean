import PPAC.Migration.Internal.StrictLookupRules

/-! 空集是总tail求值的吸收状态；该事实按全部内部索引在原对象ZF中证明。 -/
namespace PPAC.Migration.Internal.StrictLookupSink
open Source SourceAlgebra SourceLogic OmegaSyntax StructuralListProjectionSyntax
open SyntaxRenameQuerySyntax (of_eq)
open ReplacementPredicates (paramsUp)
attribute [local irreducible] NaturalRecursionSyntax.matrix

def property {m} (w n r : Fin m) : Formula m := (empty n).imp (.all
  ((iteration false w.castSucc n.castSucc r.castSucc (Fin.last m)).imp (empty (Fin.last m))))

def matrix : Formula 3 := property 0 1 2

theorem property_rename {m k} (w n r : Fin m) (ρ : Fin m → Fin k) :
    (property w n r).rename ρ = property (ρ w) (ρ n) (ρ r) := by
  simp only [property, Formula.rename, empty_rename, iteration_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem matrix_pred {m} (ρ : Fin 2 → Fin m) (x : Fin m) :
    MinimalPredicates.pred matrix ρ x = property (ρ 0) (ρ 1) x := by
  have h0 : Fin.lastCases x ρ (0 : Fin 3) = ρ 0 := by
    change Fin.lastCases x ρ (0 : Fin 2).castSucc = ρ 0
    exact Fin.lastCases_castSucc _
  have h1 : Fin.lastCases x ρ (1 : Fin 3) = ρ 1 := by
    change Fin.lastCases x ρ (1 : Fin 2).castSucc = ρ 1
    exact Fin.lastCases_castSucc _
  have h2 : Fin.lastCases x ρ (2 : Fin 3) = x := by
    change Fin.lastCases x ρ (Fin.last 2) = x
    exact Fin.lastCases_last
  simp only [matrix, MinimalPredicates.pred, property_rename, h0, h1, h2]

theorem at_value {m} {Γ : Context m} (w n r y : Fin m) (hp : Derives Γ (property w n r))
    (hn : Derives Γ (empty n)) (hy : Derives Γ (iteration false w n r y)) : Derives Γ (empty y) := by
  have hi : Derives Γ ((iteration false w n r y).imp (empty y)) := of_eq
    (by simp only [Formula.instantiate, Formula.rename, iteration_rename, empty_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq])
    (Derives.allE y (.impE hp hn))
  exact .impE hi hy

theorem selected_empty_absurd {m} {Γ : Context m} (head : Bool) (w n y : Fin m)
    (hn : Derives Γ (empty n)) (hy : Derives Γ (selected head w n y)) : Derives Γ .bot := by
  let B := body head w.castSucc n.castSucc y.castSucc (Fin.last m)
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) hy
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hPos := StructuralConsCore.positive _ _ _ _ (.conjR hB)
  have hn1 : Derives Δ (empty n.castSucc) := of_eq (empty_rename n Fin.castSucc) (under hn B)
  exact .impE hPos hn1

theorem no_cons_empty {m} {Γ : Context m} (head : Bool) (w n : Fin m)
    (hn : Derives Γ (empty n)) : Derives Γ (hasCons head w n).neg := by
  apply Derives.impI
  let C := hasCons head w n
  let B := selected head w.castSucc n.castSucc (Fin.last m)
  let Δ := Context.add B (Context.image Formula.raise (Context.add C Γ))
  apply Derives.exE (p := B) (.hyp (Or.inl rfl))
  have hn1 : Derives Δ (empty n.castSucc) := of_eq (empty_rename n Fin.castSucc) (under (add hn C) B)
  exact selected_empty_absurd head w.castSucc n.castSucc (Fin.last m) hn1 (.hyp (Or.inl rfl))

theorem empty_step {m} {Γ : Context m} (w n y : Fin m) (hn : Derives Γ (empty n))
    (hy : Derives Γ (step false w n y)) : Derives Γ (empty y) :=
  StructuralListProjection.off_cons false w n y (no_cons_empty false w n hn) hy

theorem empty_property {m} {Γ : Context m} (w n r : Fin m) (hr : Derives Γ (empty r)) :
    Derives Γ (property w n r) := by
  apply Derives.impI
  apply Derives.allI
  apply Derives.impI
  let N := empty n
  let Y := iteration false w.castSucc n.castSucc r.castSucc (Fin.last m)
  let Δ := Context.add Y (Context.image Formula.raise (Context.add N Γ))
  have hr1 : Derives Δ (empty r.castSucc) := of_eq (empty_rename r Fin.castSucc) (under (add hr N) Y)
  have hN : Derives (Context.add N Γ) N := .hyp (Or.inl rfl)
  have hn1 : Derives Δ (empty n.castSucc) := of_eq (empty_rename n Fin.castSucc) (under hN Y)
  have hEq := StructuralListProjectionRecursion.iteration_zero false w.castSucc n.castSucc r.castSucc (Fin.last m) hr1 (.hyp (Or.inl rfl))
  exact NaturalMultiplicationLaws.empty_subst n.castSucc (Fin.last m) (eq_symm hEq) hn1

theorem successor_point {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n r s y : Fin m)
    (hw : Derives Γ (omega w)) (hr : Derives Γ (.mem r w)) (hs : Derives Γ (successor s r))
    (hp : Derives Γ (property w n r)) (hn : Derives Γ (empty n))
    (hy : Derives Γ (iteration false w n s y)) : Derives Γ (empty y) := by
  have hx := StructuralListIterationTransport.exists_value hZ false w n r hw hr
  let U := iteration false w.castSucc n.castSucc r.castSucc (Fin.last m)
  let Δ := Context.add U (Context.image Formula.raise Γ)
  apply Derives.exE (p := U) hx
  have hZ1 := ZFContext.under hZ U
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw U)
  have hs1 : Derives Δ (successor s.castSucc r.castSucc) := of_eq (successor_rename s r Fin.castSucc) (under hs U)
  have hp1 : Derives Δ (property w.castSucc n.castSucc r.castSucc) := of_eq (property_rename w n r Fin.castSucc) (under hp U)
  have hn1 : Derives Δ (empty n.castSucc) := of_eq (empty_rename n Fin.castSucc) (under hn U)
  have hy1 : Derives Δ (iteration false w.castSucc n.castSucc s.castSucc y.castSucc) := of_eq (iteration_rename false w n s y Fin.castSucc) (under hy U)
  have hU : Derives Δ U := .hyp (Or.inl rfl)
  have hz := at_value w.castSucc n.castSucc r.castSucc (Fin.last m) hp1 hn1 hU
  have hStep := StructuralListProjectionRecursion.iteration_step hZ1 false w.castSucc n.castSucc r.castSucc s.castSucc (Fin.last m) y.castSucc hw1 (under hr U) hs1 hU hy1
  exact of_eq (empty_rename y Fin.castSucc).symm (empty_step w.castSucc (Fin.last m) y.castSucc hz hStep)

theorem property_successor {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n r s : Fin m)
    (hw : Derives Γ (omega w)) (hr : Derives Γ (.mem r w)) (hs : Derives Γ (successor s r))
    (hp : Derives Γ (property w n r)) : Derives Γ (property w n s) := by
  apply Derives.impI
  apply Derives.allI
  apply Derives.impI
  let N := empty n
  let Y := iteration false w.castSucc n.castSucc s.castSucc (Fin.last m)
  let Δ := Context.add Y (Context.image Formula.raise (Context.add N Γ))
  have lift {p : Formula m} (hh : Derives Γ p) : Derives Δ p.raise := under (add hh N) Y
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (lift hw)
  have hs1 : Derives Δ (successor s.castSucc r.castSucc) := of_eq (successor_rename s r Fin.castSucc) (lift hs)
  have hp1 : Derives Δ (property w.castSucc n.castSucc r.castSucc) := of_eq (property_rename w n r Fin.castSucc) (lift hp)
  have hN : Derives (Context.add N Γ) N := .hyp (Or.inl rfl)
  have hn1 : Derives Δ (empty n.castSucc) := of_eq (empty_rename n Fin.castSucc) (under hN Y)
  exact successor_point (ZFContext.under (ZFContext.add hZ N) Y) w.castSucc n.castSucc r.castSucc s.castSucc (Fin.last m)
    hw1 (lift hr) hs1 hp1 hn1 (.hyp (Or.inl rfl))

end PPAC.Migration.Internal.StrictLookupSink
