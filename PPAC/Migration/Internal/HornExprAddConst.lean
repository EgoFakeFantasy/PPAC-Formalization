import PPAC.Migration.Internal.ObjectPacketAffine

/-! The pinned original addConst expression is related to addition by object derivations.
The external index only constructs a fixed finite program; all inputs and values are internal. -/
namespace PPAC.Migration.Internal.HornExprAddConst
open Source SourceAlgebra SourceLogic OmegaSyntax HornExprSyntax ZFArithmetic
open SyntaxRenameQuerySyntax (of_eq)
open YesMetaZFC.Automation.ObjectHorn (Expr)
open YesMetaZFC.Automation

theorem backward {m n} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (k : Nat) (e : Expr n)
    (w x B y : Fin m) (env : Fin n → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat n w env))
    (hx : Derives Γ (graph e w env x)) (hB : Derives Γ (SyntaxNumeralSyntax.numeral k B))
    (hs : Derives Γ (NaturalAdditionSyntax.sum w x B y)) :
    Derives Γ (graph (ObjectPacket.Expr.addConst k e) w env y) := by
  induction k generalizing m with
  | zero =>
    have he := NaturalRecursionLaws.evaluation_zero NaturalSuccessorStep.matrix (NaturalAdditionSyntax.params w) w x B y hB hs
    exact output_subst e w x y env (eq_symm he) hx
  | succ k ih =>
    let P := (SyntaxNumeralSyntax.numeral k (Fin.last m)).conj (successor B.castSucc (Fin.last m))
    let Δ := Context.add P (Context.image Formula.raise Γ)
    apply Derives.exE (p := P) hB
    have hZ1 := ZFContext.under hZ P
    have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw P)
    have hn1 : Derives Δ (environmentNat n w.castSucc (fun i => (env i).castSucc)) :=
      of_eq (environmentNat_rename n w env Fin.castSucc) (under hn P)
    have hx1 : Derives Δ (graph e w.castSucc (fun i => (env i).castSucc) x.castSucc) :=
      of_eq (graph_rename e w x env Fin.castSucc) (under hx P)
    have hs1 : Derives Δ (NaturalAdditionSyntax.sum w.castSucc x.castSucc B.castSucc y.castSucc) :=
      of_eq (NaturalAdditionSyntax.sum_rename w x B y Fin.castSucc) (under hs P)
    have hP : Derives Δ P := .hyp (Or.inl rfl)
    have hxN := HornExprRange.range hZ1 e w.castSucc x.castSucc (fun i => (env i).castSucc) hw1 hn1 hx1
    have hbN := SyntaxNumerals.range hZ1 k w.castSucc (Fin.last m) hw1 (.conjL hP)
    have ho := add_exists hZ1 w.castSucc x.castSucc (Fin.last m) hw1 hxN hbN
    let Q := (Formula.mem (Fin.last (m+1)) w.castSucc.castSucc).conj
      (NaturalAdditionSyntax.sum w.castSucc.castSucc x.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)))
    let Ξ := Context.add Q (Context.image Formula.raise Δ)
    apply Derives.exE (p := Q) ho
    have hZ2 := ZFContext.under hZ1 Q
    have hw2 : Derives Ξ (omega w.castSucc.castSucc) :=
      of_eq (omega_rename w.castSucc Fin.castSucc) (under hw1 Q)
    have hn2 : Derives Ξ (environmentNat n w.castSucc.castSucc (fun i => (env i).castSucc.castSucc)) :=
      of_eq (environmentNat_rename n w.castSucc (fun i => (env i).castSucc) Fin.castSucc) (under hn1 Q)
    have hx2 : Derives Ξ (graph e w.castSucc.castSucc (fun i => (env i).castSucc.castSucc) x.castSucc.castSucc) :=
      of_eq (graph_rename e w.castSucc x.castSucc (fun i => (env i).castSucc) Fin.castSucc) (under hx1 Q)
    have hs2 : Derives Ξ (NaturalAdditionSyntax.sum w.castSucc.castSucc x.castSucc.castSucc B.castSucc.castSucc y.castSucc.castSucc) :=
      of_eq (NaturalAdditionSyntax.sum_rename w.castSucc x.castSucc B.castSucc y.castSucc Fin.castSucc) (under hs1 Q)
    have hP2 : Derives Ξ ((SyntaxNumeralSyntax.numeral k (Fin.last m).castSucc).conj
        (successor B.castSucc.castSucc (Fin.last m).castSucc)) := by
      simpa only [P, Formula.raise, Formula.rename, SyntaxNumeralSyntax.numeral_rename, successor_rename] using under hP Q
    have hQ : Derives Ξ Q := .hyp (Or.inl rfl)
    have hg := ih hZ2 w.castSucc.castSucc x.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))
      (fun i => (env i).castSucc.castSucc) hw2 hn2 hx2 (.conjL hP2) (.conjR hQ)
    have hyS := add_succ_forward hZ2 w.castSucc.castSucc x.castSucc.castSucc (Fin.last m).castSucc B.castSucc.castSucc
      (Fin.last (m+1)) y.castSucc.castSucc hw2 (under hxN Q) (under hbN Q) (.conjR hP2) (.conjR hQ) hs2
    have hr := intro_succ (ObjectPacket.Expr.addConst k e) w.castSucc.castSucc y.castSucc.castSucc
      (Fin.last (m+1)) (fun i => (env i).castSucc.castSucc) hg hyS
    simpa only [ObjectPacket.Expr.addConst, Formula.raise, graph_rename] using hr

theorem forward {m n} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (k : Nat) (e : Expr n)
    (w x B y : Fin m) (env : Fin n → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat n w env))
    (hx : Derives Γ (graph e w env x)) (hB : Derives Γ (SyntaxNumeralSyntax.numeral k B))
    (hy : Derives Γ (graph (ObjectPacket.Expr.addConst k e) w env y)) :
    Derives Γ (NaturalAdditionSyntax.sum w x B y) := by
  have hxN := HornExprRange.range hZ e w x env hw hn hx
  have hBN := SyntaxNumerals.range hZ k w B hw hB
  have he := add_exists hZ w x B hw hxN hBN
  let P := (Formula.mem (Fin.last m) w.castSucc).conj
    (NaturalAdditionSyntax.sum w.castSucc x.castSucc B.castSucc (Fin.last m))
  let Δ := Context.add P (Context.image Formula.raise Γ)
  apply Derives.exE (p := P) he
  have hZ1 := ZFContext.under hZ P
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw P)
  have hn1 : Derives Δ (environmentNat n w.castSucc (fun i => (env i).castSucc)) :=
    of_eq (environmentNat_rename n w env Fin.castSucc) (under hn P)
  have hx1 : Derives Δ (graph e w.castSucc (fun i => (env i).castSucc) x.castSucc) :=
    of_eq (graph_rename e w x env Fin.castSucc) (under hx P)
  have hB1 : Derives Δ (SyntaxNumeralSyntax.numeral k B.castSucc) :=
    of_eq (SyntaxNumeralSyntax.numeral_rename k B Fin.castSucc) (under hB P)
  have hy1 : Derives Δ (graph (ObjectPacket.Expr.addConst k e) w.castSucc (fun i => (env i).castSucc) y.castSucc) :=
    of_eq (graph_rename _ w y env Fin.castSucc) (under hy P)
  have hP : Derives Δ P := .hyp (Or.inl rfl)
  have hg := backward hZ1 k e w.castSucc x.castSucc B.castSucc (Fin.last m) (fun i => (env i).castSucc)
    hw1 hn1 hx1 hB1 (.conjR hP)
  have hEq := HornExprUnique.unique hZ1 (ObjectPacket.Expr.addConst k e) w.castSucc (Fin.last m) y.castSucc
    (fun i => (env i).castSucc) hw1 hn1 hg hy1
  exact of_eq (NaturalAdditionSyntax.sum_rename w x B y Fin.castSucc).symm
    (NaturalAdditionSyntax.output_subst w.castSucc x.castSucc B.castSucc (Fin.last m) y.castSucc hEq (.conjR hP))

theorem graph_iff {m n} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (k : Nat) (e : Expr n)
    (w x B y : Fin m) (env : Fin n → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat n w env))
    (hx : Derives Γ (graph e w env x)) (hB : Derives Γ (SyntaxNumeralSyntax.numeral k B)) :
    Derives Γ ((graph (ObjectPacket.Expr.addConst k e) w env y).iff (NaturalAdditionSyntax.sum w x B y)) := by
  apply Derives.conjI
  · apply Derives.impI
    exact forward (ZFContext.add hZ _) k e w x B y env (add hw _) (add hn _) (add hx _) (add hB _) (.hyp (Or.inl rfl))
  · apply Derives.impI
    exact backward (ZFContext.add hZ _) k e w x B y env (add hw _) (add hn _) (add hx _) (add hB _) (.hyp (Or.inl rfl))

end PPAC.Migration.Internal.HornExprAddConst
