import PPAC.Migration.Internal.StructuralListCheckTermination

/-! 从实际终止及原分离/基础取得首个终端；检查值保留实际内部递归见证。 -/
namespace PPAC.Migration.Internal.StructuralListCheckMinimal
open Source SourceAlgebra SourceLogic OmegaSyntax StructuralListProjectionSyntax StructuralListCheckSyntax
open ReplacementPredicates (paramsUp)
attribute [local irreducible] NaturalRecursionSyntax.matrix

def minimalAt {m} (w n r : Fin m) : Formula m :=
  ((Formula.mem r w).conj (occurs w n r)).conj (.all
    (((Formula.mem (Fin.last m) w.castSucc).conj (occurs w.castSucc n.castSucc (Fin.last m))).imp
      (Formula.mem (Fin.last m) r.castSucc).neg))

theorem minimalAt_rename {m k} (w n r : Fin m) (s : Fin m → Fin k) : (minimalAt w n r).rename s = minimalAt (s w) (s n) (s r) := by
  simp only [minimalAt, Formula.rename, Formula.neg, occurs_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem exists_minimal {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n : Fin m)
    (he : Derives Γ (eventually w n)) : Derives Γ (.ex (minimalAt w.castSucc n.castSucc (Fin.last m))) := by
  have hh : Derives Γ (MinimalPredicates.has occursMatrix (params2 w n) w) := by
    simpa only [eventually, MinimalPredicates.has, MinimalPredicates.satisfying, occursMatrix_pred, paramsUp, params2_0, params2_1] using he
  have hm := BoundedMinimal.minimal_exists occursMatrix (params2 w n) w
    (ZFContext.separation hZ occursMatrix) (ZFContext.arithmetic hZ).base.foundation hh
  simpa only [MinimalPredicates.minimalExists, MinimalPredicates.minimal, MinimalPredicates.satisfying,
    occursMatrix_pred, paramsUp, params2_0, params2_1, minimalAt] using hm

theorem minimal_law {m} {Γ : Context m} (w n r i : Fin m) (hm : Derives Γ (minimalAt w n r))
    (hi : Derives Γ (.mem i w)) (ho : Derives Γ (occurs w n i)) : Derives Γ (Formula.mem i r).neg := by
  have h : Derives Γ (((Formula.mem i w).conj (occurs w n i)).imp (Formula.mem i r).neg) := by
    simpa only [Formula.instantiate, Formula.rename, Formula.neg, occurs_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using Derives.allE i (.conjR hm)
  exact .impE h (.conjI hi ho)

theorem minimal_before {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n r : Fin m)
    (hw : Derives Γ (omega w)) (hm : Derives Γ (minimalAt w n r)) : Derives Γ (before w n r) := by
  apply Derives.allI
  apply Derives.impI
  apply Derives.impI
  let M := Formula.mem (Fin.last m) r.castSucc
  let O := occurs w.castSucc n.castSucc (Fin.last m)
  let Δ := Context.add O (Context.add M (Context.image Formula.raise Γ))
  have hZ1 : ZFContext.Evidence Δ := ZFContext.add (ZFContext.add (ZFContext.rename hZ Fin.castSucc) M) O
  have lift {p : Formula m} (hp : Derives Γ p) : Derives Δ p.raise := add (add (Derives.rename Fin.castSucc hp) M) O
  have hw1 : Derives Δ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using lift hw
  have hm1 : Derives Δ (minimalAt w.castSucc n.castSucc r.castSucc) := by simpa only [Formula.raise, minimalAt_rename] using lift hm
  have hi : Derives Δ (.mem (Fin.last m) r.castSucc) := .hyp (Or.inr (Or.inl rfl))
  have hiW := StructuralListTraceOrder.member_member hZ1 _ _ _ hw1 (.conjL (.conjL hm1)) hi
  exact .impE (minimal_law _ _ _ _ hm1 hiW (.hyp (Or.inl rfl))) hi

theorem from_termination {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n : Fin m)
    (hw : Derives Γ (omega w)) (he : Derives Γ (eventually w n)) : Derives Γ (hasCheck w n) := by
  have hm := exists_minimal hZ w n he
  let R := minimalAt w.castSucc n.castSucc (Fin.last m)
  let Ξ := Context.add R (Context.image Formula.raise Γ)
  apply Derives.exE (p := R) hm
  have hZ1 : ZFContext.Evidence Ξ := ZFContext.under hZ R
  have hw1 : Derives Ξ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw R
  have hR : Derives Ξ R := .hyp (Or.inl rfl)
  have hbefore := minimal_before hZ1 _ _ _ hw1 hR
  let B := (iteration false w.castSucc.castSucc n.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))).conj
    (terminal w.castSucc.castSucc (Fin.last (m+1)))
  let Δ := Context.add B (Context.image Formula.raise Ξ)
  have hb : Derives Ξ (.ex B) := .conjR (.conjL hR)
  apply Derives.exE (p := B) hb
  have hbfr2 : Derives Δ (before w.castSucc.castSucc n.castSucc.castSucc (Fin.last m).castSucc) := by
    simpa only [Formula.raise, before_rename] using under hbefore B
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hcheck : Derives Δ (checkedAt w.castSucc.castSucc n.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))) :=
    .conjI (.conjI (.conjI (under (.conjL (.conjL hR)) B) (.conjL hB)) (.conjR hB)) hbfr2
  have hout := intro_hasCheck _ _ _ (intro_check _ _ _ _ hcheck)
  simpa only [Formula.raise, hasCheck_rename] using hout

theorem exists_check {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n : Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (.mem n w)) : Derives Γ (hasCheck w n) :=
  from_termination hZ w n hw (StructuralListCheckTermination.at_code hZ w n hw hn)
end PPAC.Migration.Internal.StructuralListCheckMinimal
