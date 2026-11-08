import PPAC.Migration.ForcingCodeStepUnique

/-! Output uniqueness of the exact existing forcing-code interpreter, obtained
by original object member induction. This concerns all internal formula codes,
not just external ASTs. It does not assert semantic/proof correctness or Con. -/
namespace PPAC.Migration.ForcingCodeUnique
open Internal Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax
open SyntaxRenameQuerySyntax (of_eq)
open FormulaCodeSyntax (formulaCode formulaCode_rename)
open ReplacementPredicates (paramsUp)
set_option maxRecDepth 16384
attribute [local irreducible] NaturalRecursionSyntax.matrix

private theorem successor_base_subst {m} {Γ : Context m} (s x y : Fin m)
    (he : Derives Γ (.equal x y)) (hs : Derives Γ (successor s x)) : Derives Γ (successor s y) := by
  let P := successor s.castSucc (Fin.last m)
  exact of_eq (by simp only [P, Formula.instantiate, successor_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq])
    (.eqSubst P he (of_eq (by simp only [P, Formula.instantiate, successor_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hs))

private theorem step_subst {k m} {Γ : Context m}
    (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j g n : Fin m) (v u : Fin 5 → Fin m)
    (he : ∀ i, Derives Γ (.equal (v i) (u i)))
    (hs : Derives Γ (ForcingCodeStep.step R H w z f j (v 0) (v 1) (v 2) (v 3) g n (v 4))) :
    Derives Γ (ForcingCodeStep.step R H w z f j (u 0) (u 1) (u 2) (u 3) g n (u 4)) := by
  let P0 := ForcingCodeStep.step R H w.castSucc z.castSucc f.castSucc j.castSucc (Fin.last m) (v 1).castSucc (v 2).castSucc (v 3).castSucc g.castSucc n.castSucc (v 4).castSucc
  have h0 : Derives Γ (ForcingCodeStep.step R H w z f j (u 0) (v 1) (v 2) (v 3) g n (v 4)) :=
    of_eq (by simp only [P0, Formula.instantiate, ForcingCodeStep.step_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq])
      (.eqSubst P0 (he 0) (of_eq (by simp only [P0, Formula.instantiate, ForcingCodeStep.step_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hs))
  let P1 := ForcingCodeStep.step R H w.castSucc z.castSucc f.castSucc j.castSucc (u 0).castSucc (Fin.last m) (v 2).castSucc (v 3).castSucc g.castSucc n.castSucc (v 4).castSucc
  have h1 : Derives Γ (ForcingCodeStep.step R H w z f j (u 0) (u 1) (v 2) (v 3) g n (v 4)) :=
    of_eq (by simp only [P1, Formula.instantiate, ForcingCodeStep.step_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq])
      (.eqSubst P1 (he 1) (of_eq (by simp only [P1, Formula.instantiate, ForcingCodeStep.step_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) h0))
  let P2 := ForcingCodeStep.step R H w.castSucc z.castSucc f.castSucc j.castSucc (u 0).castSucc (u 1).castSucc (Fin.last m) (v 3).castSucc g.castSucc n.castSucc (v 4).castSucc
  have h2 : Derives Γ (ForcingCodeStep.step R H w z f j (u 0) (u 1) (u 2) (v 3) g n (v 4)) :=
    of_eq (by simp only [P2, Formula.instantiate, ForcingCodeStep.step_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq])
      (.eqSubst P2 (he 2) (of_eq (by simp only [P2, Formula.instantiate, ForcingCodeStep.step_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) h1))
  let P3 := ForcingCodeStep.step R H w.castSucc z.castSucc f.castSucc j.castSucc (u 0).castSucc (u 1).castSucc (u 2).castSucc (Fin.last m) g.castSucc n.castSucc (v 4).castSucc
  have h3 : Derives Γ (ForcingCodeStep.step R H w z f j (u 0) (u 1) (u 2) (u 3) g n (v 4)) :=
    of_eq (by simp only [P3, Formula.instantiate, ForcingCodeStep.step_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq])
      (.eqSubst P3 (he 3) (of_eq (by simp only [P3, Formula.instantiate, ForcingCodeStep.step_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) h2))
  let P4 := ForcingCodeStep.step R H w.castSucc z.castSucc f.castSucc j.castSucc (u 0).castSucc (u 1).castSucc (u 2).castSucc (u 3).castSucc g.castSucc n.castSucc (Fin.last m)
  have h4 : Derives Γ (ForcingCodeStep.step R H w z f j (u 0) (u 1) (u 2) (u 3) g n (u 4)) :=
    of_eq (by simp only [P4, Formula.instantiate, ForcingCodeStep.step_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq])
      (.eqSubst P4 (he 4) (of_eq (by simp only [P4, Formula.instantiate, ForcingCodeStep.step_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) h3))
  exact h4

private def rowData {k m} (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j n g t : Fin m) (v : Fin 5 → Fin m) : Formula m :=
  (ForcingCodeStep.state w (v 0) f (v 4) t).conj
    ((successor (v 1) (v 0)).conj ((successor (v 2) (v 1)).conj ((successor (v 3) (v 2)).conj
      (ForcingCodeStep.step R H w z f j (v 0) (v 1) (v 2) (v 3) g n (v 4)))))

private theorem normalize_data {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j n g t a A B C Q : Fin m) (v : Fin 5 → Fin m)
    (hw : Derives Γ (omega w)) (hA : Derives Γ (successor A a))
    (hB : Derives Γ (successor B A)) (hC : Derives Γ (successor C B))
    (hr : Derives Γ (rowData R H w z f j n g t v)) (ht : Derives Γ (ForcingCodeStep.state w a f Q t)) :
    Derives Γ (ForcingCodeStep.step R H w z f j a A B C g n Q) := by
  have es := ForcingCodeStep.state_fields hZ w (v 0) f (v 4) a f Q t hw (.conjL hr) ht
  have eA := OmegaUniversal.successor_unique (v 1) A a (ZFContext.arithmetic hZ).base.extensionality
    (successor_base_subst (v 1) (v 0) a (.conjL es) (.conjL (.conjR hr))) hA
  have eB := OmegaUniversal.successor_unique (v 2) B A (ZFContext.arithmetic hZ).base.extensionality
    (successor_base_subst (v 2) (v 1) A eA (.conjL (.conjR (.conjR hr)))) hB
  have eC := OmegaUniversal.successor_unique (v 3) C B (ZFContext.arithmetic hZ).base.extensionality
    (successor_base_subst (v 3) (v 2) B eB (.conjL (.conjR (.conjR (.conjR hr))))) hC
  let u : Fin 5 → Fin m := Fin.cases a (Fin.cases A (Fin.cases B (SyntaxAtomSyntax.two C Q)))
  have he : ∀ i, Derives Γ (.equal (v i) (u i)) := by
    intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · exact .conjL es
    · refine Fin.cases ?_ (fun i => ?_) i
      · exact eA
      · refine Fin.cases ?_ (fun i => ?_) i
        · exact eB
        · refine Fin.cases ?_ (fun i => ?_) i
          · exact eC
          · have hi : i = 0 := Subsingleton.elim _ _
            subst i
            exact .conjR es
  exact step_subst R H w z f j g n v u he (.conjR (.conjR (.conjR (.conjR hr))))

theorem row_step {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j n g t a A B C Q : Fin m)
    (hw : Derives Γ (omega w)) (hA : Derives Γ (successor A a))
    (hB : Derives Γ (successor B A)) (hC : Derives Γ (successor C B))
    (hr : Derives Γ (ForcingCodeRecursion.row R H w z f j n g t)) (ht : Derives Γ (ForcingCodeStep.state w a f Q t)) :
    Derives Γ (ForcingCodeStep.step R H w z f j a A B C g n Q) := by
  let T := rowData R H (old 5 w) (old 5 z) (old 5 f) (old 5 j) (old 5 n) (old 5 g) (old 5 t) (slot 5)
  let Δ := Context.add T (raisedContext 5 Γ)
  apply HornBinderRules.eliminate_many 5 T _ hr
  have hT : Derives Δ T := .hyp (Or.inl rfl)
  apply of_eq (ForcingCodeStep.step_rename R H w z f j a A B C g n Q (old 5)).symm
  exact normalize_data (HornBinderRules.zf_body 5 hZ T) R H
    (old 5 w) (old 5 z) (old 5 f) (old 5 j) (old 5 n) (old 5 g) (old 5 t) (old 5 a) (old 5 A) (old 5 B) (old 5 C) (old 5 Q) (slot 5)
    (of_eq (omega_rename w (old 5)) (HornBinderRules.under_body 5 hw T))
    (of_eq (successor_rename A a (old 5)) (HornBinderRules.under_body 5 hA T))
    (of_eq (successor_rename B A (old 5)) (HornBinderRules.under_body 5 hB T))
    (of_eq (successor_rename C B (old 5)) (HornBinderRules.under_body 5 hC T)) hT
    (of_eq (ForcingCodeStep.state_rename w a f Q t (old 5)) (HornBinderRules.under_body 5 ht T))

private theorem evaluation_step {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j n g v t a A B C Q : Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (OrdinalSyntax.ordinal n))
    (hA : Derives Γ (successor A a)) (hB : Derives Γ (successor B A)) (hC : Derives Γ (successor C B))
    (hg : Derives Γ (ForcingCodeRecursion.graph R H w z f j g n))
    (hv : Derives Γ (ForcingCodeRecursion.evaluation R H w z f j n v))
    (ht : Derives Γ (.mem t v)) (hs : Derives Γ (ForcingCodeStep.state w a f Q t)) :
    Derives Γ (ForcingCodeStep.step R H w z f j a A B C g n Q) := by
  let T := (ForcingCodeRecursion.graph R H w.castSucc z.castSucc f.castSucc j.castSucc (Fin.last m) n.castSucc).conj
    (ForcingCodeRecursion.value R H w.castSucc z.castSucc f.castSucc j.castSucc n.castSucc (Fin.last m) v.castSucc)
  let Δ := Context.add T (Context.image Formula.raise Γ)
  apply Derives.exE (p := T) hv
  have hT : Derives Δ T := .hyp (Or.inl rfl)
  have hg1 := of_eq (ForcingCodeRecursion.graph_rename R H w z f j g n Fin.castSucc) (under hg T)
  have hn1 := of_eq (OrdinalSyntax.ordinal_rename n Fin.castSucc) (under hn T)
  have eg := ForcingCodeRecursion.graph_unique (ZFContext.under hZ T) R H w.castSucc z.castSucc f.castSucc j.castSucc
    (Fin.last m) g.castSucc n.castSucc hn1 (.conjL hT) hg1
  let P := ForcingCodeRecursion.value R H w.castSucc.castSucc z.castSucc.castSucc f.castSucc.castSucc j.castSucc.castSucc
    n.castSucc.castSucc (Fin.last (m+1)) v.castSucc.castSucc
  have hval : Derives Δ (ForcingCodeRecursion.value R H w.castSucc z.castSucc f.castSucc j.castSucc n.castSucc g.castSucc v.castSucc) :=
    of_eq (by simp only [P, Formula.instantiate, ForcingCodeRecursion.value_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq])
      (.eqSubst P eg (of_eq (by simp only [P, Formula.instantiate, ForcingCodeRecursion.value_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (.conjR hT)))
  have hrow := Derives.conjR (.impE (.conjL (ForcingCodeRecursion.value_at R H w.castSucc z.castSucc f.castSucc j.castSucc n.castSucc g.castSucc v.castSucc t.castSucc hval)) (under ht T))
  apply of_eq (ForcingCodeStep.step_rename R H w z f j a A B C g n Q Fin.castSucc).symm
  exact row_step (ZFContext.under hZ T) R H w.castSucc z.castSucc f.castSucc j.castSucc n.castSucc g.castSucc t.castSucc a.castSucc A.castSucc B.castSucc C.castSucc Q.castSucc
    (of_eq (omega_rename w Fin.castSucc) (under hw T))
    (of_eq (successor_rename A a Fin.castSucc) (under hA T))
    (of_eq (successor_rename B A Fin.castSucc) (under hB T))
    (of_eq (successor_rename C B Fin.castSucc) (under hC T)) hrow
    (of_eq (ForcingCodeStep.state_rename w a f Q t Fin.castSucc) (under hs T))

theorem compiled_step {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j n g a A B C Q : Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (OrdinalSyntax.ordinal n))
    (hA : Derives Γ (successor A a)) (hB : Derives Γ (successor B A)) (hC : Derives Γ (successor C B))
    (hg : Derives Γ (ForcingCodeRecursion.graph R H w z f j g n))
    (hq : Derives Γ (ForcingCodeRecursion.compiled R H w z f j a n Q)) :
    Derives Γ (ForcingCodeStep.step R H w z f j a A B C g n Q) := by
  let T := (ForcingCodeRecursion.evaluation R H (old 2 w) (old 2 z) (old 2 f) (old 2 j) (old 2 n) (slot 2 0)).conj
    ((Formula.mem (slot 2 1) (slot 2 0)).conj (ForcingCodeStep.state (old 2 w) (old 2 a) (old 2 f) (old 2 Q) (slot 2 1)))
  let Δ := Context.add T (raisedContext 2 Γ)
  apply HornBinderRules.eliminate_many 2 T _ hq
  have hT : Derives Δ T := .hyp (Or.inl rfl)
  apply of_eq (ForcingCodeStep.step_rename R H w z f j a A B C g n Q (old 2)).symm
  exact evaluation_step (HornBinderRules.zf_body 2 hZ T) R H
    (old 2 w) (old 2 z) (old 2 f) (old 2 j) (old 2 n) (old 2 g) (slot 2 0) (slot 2 1) (old 2 a) (old 2 A) (old 2 B) (old 2 C) (old 2 Q)
    (of_eq (omega_rename w (old 2)) (HornBinderRules.under_body 2 hw T))
    (of_eq (OrdinalSyntax.ordinal_rename n (old 2)) (HornBinderRules.under_body 2 hn T))
    (of_eq (successor_rename A a (old 2)) (HornBinderRules.under_body 2 hA T))
    (of_eq (successor_rename B A (old 2)) (HornBinderRules.under_body 2 hB T))
    (of_eq (successor_rename C B (old 2)) (HornBinderRules.under_body 2 hC T))
    (of_eq (ForcingCodeRecursion.graph_rename R H w z f j g n (old 2)) (HornBinderRules.under_body 2 hg T))
    (.conjL hT) (.conjL (.conjR hT)) (.conjR (.conjR hT))
private def params {m} (w z f j : Fin m) : Fin 4 → Fin m := Fin.cases w (Fin.cases z (SyntaxAtomSyntax.two f j))
private theorem params_map {m l} (w z f j : Fin m) (r : Fin m → Fin l) :
    (fun i => r (params w z f j i)) = params (r w) (r z) (r f) (r j) := by
  funext i
  exact Fin.cases rfl (fun i => Fin.cases rfl (fun i => Fin.cases rfl (fun i => Fin.cases rfl (fun b => Fin.elim0 b) i) i) i) i

private def property {k m} (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j n : Fin m) : Formula m := .all (.all (.all
  ((ForcingCodeRecursion.compiled R H w.castSucc.castSucc.castSucc z.castSucc.castSucc.castSucc f.castSucc.castSucc.castSucc j.castSucc.castSucc.castSucc
      (Fin.last m).castSucc.castSucc n.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc).imp
    ((ForcingCodeRecursion.compiled R H w.castSucc.castSucc.castSucc z.castSucc.castSucc.castSucc f.castSucc.castSucc.castSucc j.castSucc.castSucc.castSucc
      (Fin.last m).castSucc.castSucc n.castSucc.castSucc.castSucc (Fin.last (m+2))).imp
      (.equal (Fin.last (m+1)).castSucc (Fin.last (m+2)))))))
private theorem property_rename {k m l} (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j n : Fin m) (r : Fin m → Fin l) :
    (property R H w z f j n).rename r = property R H (r w) (r z) (r f) (r j) (r n) := by
  simp only [property, Formula.rename, ForcingCodeRecursion.compiled_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]
private theorem property_at {k m} {Γ : Context m} (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j n a Q V : Fin m)
    (hp : Derives Γ (property R H w z f j n))
    (hq : Derives Γ (ForcingCodeRecursion.compiled R H w z f j a n Q))
    (hv : Derives Γ (ForcingCodeRecursion.compiled R H w z f j a n V)) : Derives Γ (.equal Q V) := by
  have hi : Derives Γ ((ForcingCodeRecursion.compiled R H w z f j a n Q).imp
      ((ForcingCodeRecursion.compiled R H w z f j a n V).imp (.equal Q V))) :=
    of_eq (by simp only [Formula.instantiate, Formula.rename, ForcingCodeRecursion.compiled_rename,
      Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (Derives.allE V (Derives.allE Q (Derives.allE a hp)))
  exact .impE (.impE hi hq) hv

private def curried {k m} (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j n : Fin m) : Formula m := .all
  ((Formula.mem (Fin.last m) w.castSucc).imp ((Formula.mem (Fin.last m) n.castSucc).imp
    (property R H w.castSucc z.castSucc f.castSucc j.castSucc (Fin.last m))))
private theorem curried_rename {k m l} (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j n : Fin m) (r : Fin m → Fin l) :
    (curried R H w z f j n).rename r = curried R H (r w) (r z) (r f) (r j) (r n) := by
  simp only [curried, Formula.rename, property_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]
private theorem curried_at {k m} {Γ : Context m} (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j n x : Fin m)
    (hp : Derives Γ (curried R H w z f j n)) (hx : Derives Γ (.mem x w)) (hn : Derives Γ (.mem x n)) :
    Derives Γ (property R H w z f j x) := by
  have hi : Derives Γ ((Formula.mem x w).imp ((Formula.mem x n).imp (property R H w z f j x))) :=
    of_eq (by simp only [Formula.instantiate, Formula.rename, property_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (Derives.allE x hp)
  exact .impE (.impE hi hx) hn

private theorem functional_from_induction {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j n g : Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (.mem n w))
    (hg : Derives Γ (ForcingCodeRecursion.graph R H w z f j g n))
    (hi : Derives Γ (curried R H w z f j n)) : Derives Γ (ForcingCodeStepUnique.functional w f g n) := by
  apply Derives.allI
  apply Derives.allI
  apply Derives.allI
  apply Derives.allI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let T := Formula.mem (slot 4 0) (old 4 n)
  let P := ForcingCodeStep.read (old 4 w) (old 4 g) (slot 4 0) (slot 4 1) (old 4 f) (slot 4 2)
  let V := ForcingCodeStep.read (old 4 w) (old 4 g) (slot 4 0) (slot 4 1) (old 4 f) (slot 4 3)
  let Δ := Context.add V (Context.add P (Context.add T (raisedContext 4 Γ)))
  have hw4 : Derives Δ (omega (old 4 w)) := of_eq (omega_rename w (old 4)) (add (add (add (HornBinderRules.under_many 4 hw) T) P) V)
  have hn4 : Derives Δ (.mem (old 4 n) (old 4 w)) := add (add (add (HornBinderRules.under_many 4 hn) T) P) V
  have hg4 : Derives Δ (ForcingCodeRecursion.graph R H (old 4 w) (old 4 z) (old 4 f) (old 4 j) (old 4 g) (old 4 n)) :=
    of_eq (ForcingCodeRecursion.graph_rename R H w z f j g n (old 4)) (add (add (add (HornBinderRules.under_many 4 hg) T) P) V)
  have hi4 : Derives Δ (curried R H (old 4 w) (old 4 z) (old 4 f) (old 4 j) (old 4 n)) :=
    of_eq (curried_rename R H w z f j n (old 4)) (add (add (add (HornBinderRules.under_many 4 hi) T) P) V)
  have hZ4 := ZFContext.add (ZFContext.add (ZFContext.add (HornBinderRules.zf_many 4 hZ) T) P) V
  have hx : Derives Δ T := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have hp : Derives Δ P := .hyp (Or.inr (Or.inl rfl))
  have hv : Derives Δ V := .hyp (Or.inl rfl)
  have ht := OmegaStructureInduction.omega_transitive (old 4 w) (ZFContext.separation hZ4 OmegaStructureSyntax.subsetMatrix) hw4
  have hb := Derives.impE (OmegaStructureSyntax.transitive_at (old 4 w) (old 4 n) ht) hn4
  have hxw := Derives.impE (RestrictionSyntax.subset_at (old 4 n) (old 4 w) (slot 4 0) hb) hx
  have hno := NaturalOrderBasic.ordinal hZ4 (old 4 w) (old 4 n) hw4 hn4
  have hq1 := ForcingCodeRecursion.read_to_compiled hZ4 R H (old 4 w) (old 4 z) (old 4 f) (old 4 j) (old 4 g) (old 4 n)
    (slot 4 1) (slot 4 0) (slot 4 2) hno hx hg4 hp
  have hv1 := ForcingCodeRecursion.read_to_compiled hZ4 R H (old 4 w) (old 4 z) (old 4 f) (old 4 j) (old 4 g) (old 4 n)
    (slot 4 1) (slot 4 0) (slot 4 3) hno hx hg4 hv
  have hc := curried_at R H (old 4 w) (old 4 z) (old 4 f) (old 4 j) (old 4 n) (slot 4 0) hi4 hxw hx
  exact property_at R H (old 4 w) (old 4 z) (old 4 f) (old 4 j) (slot 4 0) (slot 4 1) (slot 4 2) (slot 4 3) hc hq1 hv1

private structure Inputs {k m} (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (Γ : Context m) (w z f j n g : Fin m) : Prop where
  hw : Derives Γ (omega w)
  hn : Derives Γ (OrdinalSyntax.ordinal n)
  hg : Derives Γ (ForcingCodeRecursion.graph R H w z f j g n)
  he : Derives Γ (ForcingCodeStepUnique.functional w f g n)
private theorem underInputs {k m} {Γ : Context m} (R : Source.Formula (k+2)) (H : Source.Formula (k+1))
    {w z f j n g : Fin m} (hI : Inputs R H Γ w z f j n g) (T : Formula (m+1)) :
    Inputs R H (Context.add T (Context.image Formula.raise Γ)) w.castSucc z.castSucc f.castSucc j.castSucc n.castSucc g.castSucc := by
  exact ⟨of_eq (omega_rename w Fin.castSucc) (under hI.hw T),
    of_eq (OrdinalSyntax.ordinal_rename n Fin.castSucc) (under hI.hn T),
    of_eq (ForcingCodeRecursion.graph_rename R H w z f j g n Fin.castSucc) (under hI.hg T),
    of_eq (ForcingCodeStepUnique.functional_rename w f g n Fin.castSucc) (under hI.he T)⟩

private theorem scope_stage3 {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j n g a A B C Q V : Fin m) (hI : Inputs R H Γ w z f j n g)
    (hA : Derives Γ (successor A a)) (hB : Derives Γ (successor B A)) (hC : Derives Γ (successor C B))
    (hq : Derives Γ (ForcingCodeRecursion.compiled R H w z f j a n Q))
    (hv : Derives Γ (ForcingCodeRecursion.compiled R H w z f j a n V)) : Derives Γ (.equal Q V) := by
  exact ForcingCodeStepUnique.unique hZ R H w z f j a A B C g n Q V hI.hw hI.he
    (compiled_step hZ R H w z f j n g a A B C Q hI.hw hI.hn hA hB hC hI.hg hq)
    (compiled_step hZ R H w z f j n g a A B C V hI.hw hI.hn hA hB hC hI.hg hv)

private theorem scope_stage2 {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j n g a A B Q V : Fin m) (hI : Inputs R H Γ w z f j n g)
    (hA : Derives Γ (successor A a))
    (hB : Derives Γ (successor B A))
    (hq : Derives Γ (ForcingCodeRecursion.compiled R H w z f j a n Q))
    (hv : Derives Γ (ForcingCodeRecursion.compiled R H w z f j a n V)) : Derives Γ (.equal Q V) := by
  let T := successor (Fin.last m) B.castSucc
  let Δ := Context.add T (Context.image Formula.raise Γ)
  apply Derives.exE (p := T) (InsertExistence.exists_insert B B (ZFContext.arithmetic hZ).base.pairing (ZFContext.arithmetic hZ).base.union)
  have hT : Derives Δ T := .hyp (Or.inl rfl)
  exact scope_stage3 (ZFContext.under hZ T) R H w.castSucc z.castSucc f.castSucc j.castSucc n.castSucc g.castSucc a.castSucc A.castSucc B.castSucc (Fin.last m) Q.castSucc V.castSucc (underInputs R H hI T)
    (of_eq (successor_rename A a Fin.castSucc) (under hA T))
    (of_eq (successor_rename B A Fin.castSucc) (under hB T))
    hT (of_eq (ForcingCodeRecursion.compiled_rename R H w z f j a n Q Fin.castSucc) (under hq T))
    (of_eq (ForcingCodeRecursion.compiled_rename R H w z f j a n V Fin.castSucc) (under hv T))

private theorem scope_stage1 {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j n g a A Q V : Fin m) (hI : Inputs R H Γ w z f j n g)
    (hA : Derives Γ (successor A a))
    (hq : Derives Γ (ForcingCodeRecursion.compiled R H w z f j a n Q))
    (hv : Derives Γ (ForcingCodeRecursion.compiled R H w z f j a n V)) : Derives Γ (.equal Q V) := by
  let T := successor (Fin.last m) A.castSucc
  let Δ := Context.add T (Context.image Formula.raise Γ)
  apply Derives.exE (p := T) (InsertExistence.exists_insert A A (ZFContext.arithmetic hZ).base.pairing (ZFContext.arithmetic hZ).base.union)
  have hT : Derives Δ T := .hyp (Or.inl rfl)
  exact scope_stage2 (ZFContext.under hZ T) R H w.castSucc z.castSucc f.castSucc j.castSucc n.castSucc g.castSucc a.castSucc A.castSucc (Fin.last m) Q.castSucc V.castSucc (underInputs R H hI T)
    (of_eq (successor_rename A a Fin.castSucc) (under hA T))
    hT (of_eq (ForcingCodeRecursion.compiled_rename R H w z f j a n Q Fin.castSucc) (under hq T))
    (of_eq (ForcingCodeRecursion.compiled_rename R H w z f j a n V Fin.castSucc) (under hv T))

private theorem scope_stage0 {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j n g a Q V : Fin m) (hI : Inputs R H Γ w z f j n g)
    (hq : Derives Γ (ForcingCodeRecursion.compiled R H w z f j a n Q))
    (hv : Derives Γ (ForcingCodeRecursion.compiled R H w z f j a n V)) : Derives Γ (.equal Q V) := by
  let T := successor (Fin.last m) a.castSucc
  let Δ := Context.add T (Context.image Formula.raise Γ)
  apply Derives.exE (p := T) (InsertExistence.exists_insert a a (ZFContext.arithmetic hZ).base.pairing (ZFContext.arithmetic hZ).base.union)
  have hT : Derives Δ T := .hyp (Or.inl rfl)
  exact scope_stage1 (ZFContext.under hZ T) R H w.castSucc z.castSucc f.castSucc j.castSucc n.castSucc g.castSucc a.castSucc (Fin.last m) Q.castSucc V.castSucc (underInputs R H hI T)
    hT (of_eq (ForcingCodeRecursion.compiled_rename R H w z f j a n Q Fin.castSucc) (under hq T))
    (of_eq (ForcingCodeRecursion.compiled_rename R H w z f j a n V Fin.castSucc) (under hv T))

private theorem property_from_below {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j n : Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (.mem n w))
    (hi : Derives Γ (curried R H w z f j n)) : Derives Γ (property R H w z f j n) := by
  have hno := NaturalOrderBasic.ordinal hZ w n hw hn
  let G := ForcingCodeRecursion.graph R H w.castSucc z.castSucc f.castSucc j.castSucc (Fin.last m) n.castSucc
  let Δ := Context.add G (Context.image Formula.raise Γ)
  apply Derives.exE (p := G) (ForcingCodeRecursion.exists_graph hZ R H w z f j n hno)
  have hG : Derives Δ G := .hyp (Or.inl rfl)
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw G)
  have hn1 : Derives Δ (.mem n.castSucc w.castSucc) := under hn G
  have hi1 := of_eq (curried_rename R H w z f j n Fin.castSucc) (under hi G)
  have hno1 := of_eq (OrdinalSyntax.ordinal_rename n Fin.castSucc) (under hno G)
  have he := functional_from_induction (ZFContext.under hZ G) R H w.castSucc z.castSucc f.castSucc j.castSucc n.castSucc (Fin.last m) hw1 hn1 hG hi1
  apply of_eq (property_rename R H w z f j n Fin.castSucc).symm
  apply Derives.allI
  apply Derives.allI
  apply Derives.allI
  apply Derives.impI
  apply Derives.impI
  let P := ForcingCodeRecursion.compiled R H (old 3 w.castSucc) (old 3 z.castSucc) (old 3 f.castSucc) (old 3 j.castSucc) (slot 3 0) (old 3 n.castSucc) (slot 3 1)
  let V := ForcingCodeRecursion.compiled R H (old 3 w.castSucc) (old 3 z.castSucc) (old 3 f.castSucc) (old 3 j.castSucc) (slot 3 0) (old 3 n.castSucc) (slot 3 2)
  let Ξ := Context.add V (Context.add P (raisedContext 3 Δ))
  have hI : Inputs R H Ξ (old 3 w.castSucc) (old 3 z.castSucc) (old 3 f.castSucc) (old 3 j.castSucc) (old 3 n.castSucc) (old 3 (Fin.last m)) :=
    ⟨of_eq (omega_rename w.castSucc (old 3)) (add (add (HornBinderRules.under_many 3 hw1) P) V),
      of_eq (OrdinalSyntax.ordinal_rename n.castSucc (old 3)) (add (add (HornBinderRules.under_many 3 hno1) P) V),
      of_eq (ForcingCodeRecursion.graph_rename R H w.castSucc z.castSucc f.castSucc j.castSucc (Fin.last m) n.castSucc (old 3)) (add (add (HornBinderRules.under_many 3 hG) P) V),
      of_eq (ForcingCodeStepUnique.functional_rename w.castSucc f.castSucc (Fin.last m) n.castSucc (old 3)) (add (add (HornBinderRules.under_many 3 he) P) V)⟩
  exact scope_stage0 (ZFContext.add (ZFContext.add (HornBinderRules.zf_many 3 (ZFContext.under hZ G)) P) V) R H
    (old 3 w.castSucc) (old 3 z.castSucc) (old 3 f.castSucc) (old 3 j.castSucc) (old 3 n.castSucc) (old 3 (Fin.last m))
    (slot 3 0) (slot 3 1) (slot 3 2) hI (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

private def propertyMatrix {k} (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) : Formula (4+1) :=
  property R H (0 : Fin 4).castSucc (1 : Fin 4).castSucc (2 : Fin 4).castSucc (3 : Fin 4).castSucc (Fin.last 4)
private theorem matrix_pred {k m} (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (ρ : Fin 4 → Fin m) (n : Fin m) :
    MinimalPredicates.pred (propertyMatrix R H) ρ n = property R H (ρ 0) (ρ 1) (ρ 2) (ρ 3) n := by
  simp only [MinimalPredicates.pred, propertyMatrix, property_rename, Fin.lastCases_last, Fin.lastCases_castSucc]

private theorem progressive {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j : Fin m)
    (hw : Derives Γ (omega w)) :
    Derives Γ (BoundedInduction.progressive (propertyMatrix R H) (params w z f j) w) := by
  simp only [BoundedInduction.progressive, BoundedInduction.below, matrix_pred, paramsUp]
  apply Derives.allI
  apply Derives.impI
  apply Derives.impI
  let M := Formula.mem (Fin.last m) w.castSucc
  let I := curried R H w.castSucc z.castSucc f.castSucc j.castSucc (Fin.last m)
  let Δ := Context.add I (Context.add M (Context.image Formula.raise Γ))
  have hZ1 := ZFContext.add (ZFContext.add (ZFContext.rename hZ Fin.castSucc) M) I
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (add (add (Derives.rename Fin.castSucc hw) M) I)
  exact property_from_below hZ1 R H w.castSucc z.castSucc f.castSucc j.castSucc (Fin.last m) hw1 (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

private theorem all_properties {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j : Fin m)
    (hw : Derives Γ (omega w)) :
    Derives Γ (.all ((Formula.mem (Fin.last m) w.castSucc).imp (property R H w.castSucc z.castSucc f.castSucc j.castSucc (Fin.last m)))) := by
  have he := BoundedInduction.induction_on_set (propertyMatrix R H) (params w z f j) w
    (ZFContext.separation hZ (propertyMatrix R H).neg) (ZFContext.arithmetic hZ).base.foundation
    (progressive hZ R H w z f j hw)
  exact of_eq (by simp only [BoundedInduction.holds, matrix_pred, paramsUp]; rfl) he

/-- Two independent candidates in the actual recursive relation are equal.
Only internal omega membership of the input is required, with no supplied
history, availability, earlier-read functionality or selected execution. -/
theorem unique {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j a n Q V : Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (.mem n w))
    (hq : Derives Γ (ForcingCodeRecursion.compiled R H w z f j a n Q))
    (hv : Derives Γ (ForcingCodeRecursion.compiled R H w z f j a n V)) : Derives Γ (.equal Q V) := by
  have hp : Derives Γ ((Formula.mem n w).imp (property R H w z f j n)) :=
    of_eq (by simp only [Formula.instantiate, Formula.rename, property_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq])
      (Derives.allE n (all_properties hZ R H w z f j hw))
  exact property_at R H w z f j n a Q V (.impE hp hn) hq hv

def sentence {k m} (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j a n Q V : Fin m) : Source.Sentence :=
  ((omega w).imp ((Formula.mem n w).imp ((ForcingCodeRecursion.compiled R H w z f j a n Q).imp
    ((ForcingCodeRecursion.compiled R H w z f j a n V).imp (.equal Q V))))).close

theorem kernel_certificate {k m} (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j a n Q V : Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence (sentence R H w z f j a n Q V)) := by
  apply ZFReplay.replay
  apply TheoryTransport.sentence
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  exact unique (ZFContext.add (ZFContext.add (ZFContext.add (ZFContext.add (ZFContext.source_ZF m) _) _) _) _) R H w z f j a n Q V
    (.hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) (.hyp (Or.inr (Or.inr (Or.inl rfl))))
    (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

def uniqueOutput {k m} (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j a n Q : Fin m) : Formula m := .all
  ((ForcingCodeRecursion.compiled R H w.castSucc z.castSucc f.castSucc j.castSucc a.castSucc n.castSucc (Fin.last m)).imp
    (.equal (Fin.last m) Q.castSucc))
theorem uniqueOutput_rename {k m l} (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j a n Q : Fin m) (r : Fin m → Fin l) :
    (uniqueOutput R H w z f j a n Q).rename r = uniqueOutput R H (r w) (r z) (r f) (r j) (r a) (r n) (r Q) := by
  simp only [uniqueOutput, Formula.rename, ForcingCodeRecursion.compiled_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

private theorem unique_output {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j a n Q : Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (.mem n w))
    (hq : Derives Γ (ForcingCodeRecursion.compiled R H w z f j a n Q)) : Derives Γ (uniqueOutput R H w z f j a n Q) := by
  apply Derives.allI
  apply Derives.impI
  let T := ForcingCodeRecursion.compiled R H w.castSucc z.castSucc f.castSucc j.castSucc a.castSucc n.castSucc (Fin.last m)
  exact unique (ZFContext.under hZ T) R H w.castSucc z.castSucc f.castSucc j.castSucc a.castSucc n.castSucc (Fin.last m) Q.castSucc
    (of_eq (omega_rename w Fin.castSucc) (under hw T)) (under hn T) (.hyp (Or.inl rfl))
    (of_eq (ForcingCodeRecursion.compiled_rename R H w z f j a n Q Fin.castSucc) (under hq T))

/-- Exactly one well-typed output of the actual recursive interpreter. -/
def typedUniqueOutput {k m} (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j a n : Fin m) : Formula m := .ex
  ((ForcingCodeRecursion.compiled R H w.castSucc z.castSucc f.castSucc j.castSucc a.castSucc n.castSucc (Fin.last m)).conj
    ((formulaCode w.castSucc (Fin.last m) a.castSucc f.castSucc).conj
      (uniqueOutput R H w.castSucc z.castSucc f.castSucc j.castSucc a.castSucc n.castSucc (Fin.last m))))
theorem typedUniqueOutput_rename {k m l} (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j a n : Fin m) (r : Fin m → Fin l) :
    (typedUniqueOutput R H w z f j a n).rename r = typedUniqueOutput R H (r w) (r z) (r f) (r j) (r a) (r n) := by
  simp only [typedUniqueOutput, Formula.rename, ForcingCodeRecursion.compiled_rename, formulaCode_rename, uniqueOutput_rename,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem typed_unique_total {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j a n : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hf : Derives Γ (SyntaxNumeralSyntax.numeral (k+2) f)) (hj : Derives Γ (SyntaxNumeralSyntax.numeral (k+1) j))
    (hc : Derives Γ (formulaCode w n a z)) : Derives Γ (typedUniqueOutput R H w z f j a n) := by
  let T := ForcingCodeRecursion.compiled R H w.castSucc z.castSucc f.castSucc j.castSucc a.castSucc n.castSucc (Fin.last m)
  let Δ := Context.add T (Context.image Formula.raise Γ)
  apply Derives.exE (p := T) (ForcingCodeTotal.total hZ R H w z f j a n hw hz hf hj hc)
  have hT : Derives Δ T := .hyp (Or.inl rfl)
  have ht := ForcingCodeRecursion.target_type R H w.castSucc z.castSucc f.castSucc j.castSucc a.castSucc n.castSucc (Fin.last m) hT
  have hn := Derives.conjL (FormulaCodeProperties.guards w n a z hc)
  have hu := unique_output (ZFContext.under hZ T) R H w.castSucc z.castSucc f.castSucc j.castSucc a.castSucc n.castSucc (Fin.last m)
    (of_eq (omega_rename w Fin.castSucc) (under hw T)) (under hn T) hT
  have ho : Derives Δ (typedUniqueOutput R H w.castSucc z.castSucc f.castSucc j.castSucc a.castSucc n.castSucc) := by
    apply Derives.exI (Fin.last m)
    exact of_eq (by simp only [T, Formula.instantiate, Formula.rename, ForcingCodeRecursion.compiled_rename, formulaCode_rename,
      uniqueOutput_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (.conjI hT (.conjI ht hu))
  exact of_eq (typedUniqueOutput_rename R H w z f j a n Fin.castSucc).symm ho

def totalSentence {k m} (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j a n : Fin m) : Source.Sentence :=
  ((omega w).imp ((empty z).imp ((SyntaxNumeralSyntax.numeral (k+2) f).imp ((SyntaxNumeralSyntax.numeral (k+1) j).imp
    ((formulaCode w n a z).imp (typedUniqueOutput R H w z f j a n)))))).close

theorem total_kernel_certificate {k m} (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j a n : Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence (totalSentence R H w z f j a n)) := by
  apply ZFReplay.replay
  apply TheoryTransport.sentence
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  exact typed_unique_total (ZFContext.add (ZFContext.add (ZFContext.add (ZFContext.add (ZFContext.add (ZFContext.source_ZF m) _) _) _) _) _) R H w z f j a n
    (.hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))) (.hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
    (.hyp (Or.inr (Or.inr (Or.inl rfl)))) (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))
end PPAC.Migration.ForcingCodeUnique
