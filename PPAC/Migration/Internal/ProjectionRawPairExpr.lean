import PPAC.Migration.Internal.ProjectionTracePremises
import PPAC.Migration.Internal.RawCodeProjection

/-! 任意原始标签与裸配数载荷的实际Expr图，保留非规范外壳的head／tail数值。 -/
namespace PPAC.Migration.Internal.ProjectionRawPairExpr
open Source SourceAlgebra SourceLogic OmegaSyntax HornExprSyntax
open SyntaxRenameQuerySyntax (of_eq)
open YesMetaZFC.Automation.ObjectHorn (Expr)

def rawPair {a} (tag first rest : Fin a) : Expr a := .succ (.pair (.var tag) (.pair (.var first) (.var rest)))

theorem graph_of_code {m a} {Γ : Context m} (tag first rest : Fin a) (w p x : Fin m) (env : Fin a → Fin m)
    (hn : Derives Γ (environmentNat a w env)) (hp : Derives Γ (GodelPairSyntax.code w (env first) (env rest) p))
    (hr : Derives Γ (StructuralNodeSyntax.raw w (env tag) p x)) : Derives Γ (graph (rawPair tag first rest) w env x) := by
  have hv (j : Fin a) : Derives Γ (graph (.var j) w env (env j)) := .conjI (environmentNat_at w env hn j) (.eqRefl _)
  exact HornExprStructural.raw_graph (.var tag) (.pair (.var first) (.var rest)) w (env tag) p x env (hv tag)
    (intro_pair (.var first) (.var rest) w p (env first) (env rest) env (hv first) (hv rest) hp) hr

theorem head_tail {m a} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (head : Bool) (tag first rest : Fin a)
    (w x : Fin m) (env : Fin a → Fin m) (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat a w env))
    (hx : Derives Γ (graph (rawPair tag first rest) w env x)) :
    Derives Γ (RawCodeProjectionSyntax.step head w x (if head then env first else env rest)) := by
  have he := GodelPairCore.exists_code hZ w (env first) (env rest) hw (environmentNat_at w env hn first) (environmentNat_at w env hn rest)
  let B := (Formula.mem (Fin.last m) w.castSucc).conj (GodelPairSyntax.code w.castSucc (env first).castSucc (env rest).castSucc (Fin.last m))
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) he
  have hZ1 := ZFContext.under hZ B
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw B)
  have hn1 := of_eq (environmentNat_rename a w env Fin.castSucc) (under hn B)
  have hx1 := of_eq (graph_rename (rawPair tag first rest) w x env Fin.castSucc) (under hx B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hv (j : Fin a) : Derives Δ (graph (.var j) w.castSucc (fun i => (env i).castSucc) (env j).castSucc) := .conjI (environmentNat_at _ _ hn1 j) (.eqRefl _)
  have hp := intro_pair (.var first) (.var rest) w.castSucc (Fin.last m) (env first).castSucc (env rest).castSucc (fun i => (env i).castSucc)
    (hv first) (hv rest) (.conjR hB)
  have hr := Derives.impE (.conjL (HornExprStructural.raw_iff hZ1 (.var tag) (.pair (.var first) (.var rest))
    w.castSucc (env tag).castSucc (Fin.last m) x.castSucc (fun i => (env i).castSucc) hw1 hn1 (hv tag) hp)) hx1
  have ho := RawCodeProjection.intro_raw_pair head w.castSucc (env tag).castSucc (Fin.last m) (env first).castSucc (env rest).castSucc x.castSucc
    (environmentNat_at _ _ hn1 tag) (.conjL hB) (environmentNat_at _ _ hn1 first) (environmentNat_at _ _ hn1 rest) hr (.conjR hB)
  cases head <;> exact of_eq (RawCodeProjectionSyntax.step_rename _ w x _ Fin.castSucc).symm ho

theorem successor_variable_iff {m a} {Γ : Context m} (j : Fin a) (w s : Fin m) (env : Fin a → Fin m)
    (hn : Derives Γ (environmentNat a w env)) :
    Derives Γ ((graph (.succ (.var j)) w env s).iff (successor s (env j))) := by
  apply Derives.conjI
  · apply Derives.impI
    let E := graph (.succ (.var j)) w env s
    let B := (graph (.var j) w.castSucc (fun i => (env i).castSucc) (Fin.last m)).conj (successor s.castSucc (Fin.last m))
    let Δ := Context.add B (Context.image Formula.raise (Context.add E Γ))
    apply Derives.exE (p := B) (.hyp (Or.inl rfl))
    have hB : Derives Δ B := .hyp (Or.inl rfl)
    have ho := GodelUnpairArithmetic.successor_base_subst s.castSucc (Fin.last m) (env j).castSucc (.conjR (.conjL hB)) (.conjR hB)
    exact of_eq (successor_rename s (env j) Fin.castSucc).symm ho
  · apply Derives.impI
    exact intro_succ (.var j) w s (env j) env (.conjI (add (environmentNat_at w env hn j) _) (.eqRefl _)) (.hyp (Or.inl rfl))

end PPAC.Migration.Internal.ProjectionRawPairExpr
