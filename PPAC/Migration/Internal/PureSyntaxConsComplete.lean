import PPAC.Migration.Internal.PureSyntaxArgumentSound
import PPAC.Migration.Internal.PureSyntaxTermCorrectness

/-! 合法cons的完整查询构造：实际选择子行与父行，消去所有轨迹／编码行见证。 -/
namespace PPAC.Migration.Internal.PureSyntaxConsComplete
open Source SourceAlgebra SourceLogic OmegaSyntax HornExprSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem from_rows {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w k n p q : Fin m) (env : Fin 5 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 5 w env))
    (hk : Derives Γ (successor k (env 2))) (hc : Derives Γ (StructuralListSyntax.consCode w (env 3) (env 4) n))
    (hp : Derives Γ (PureSyntaxTrace.termRow w (env 0) (env 1) (env 3) p))
    (hq : Derives Γ (PureSyntaxTrace.argumentRow w (env 0) (env 1) (env 2) (env 4) q))
    (hcp : Derives Γ (PureSyntaxTrace.condition w p)) (hcq : Derives Γ (PureSyntaxTrace.condition w q)) :
    Derives Γ (PureSyntaxTrace.arguments w (env 0) (env 1) k n) := by
  have hkn := OmegaStructureAlgebra.successor_member w k (env 2) (ZFContext.arithmetic hZ).base.extensionality hw (environmentNat_at w env hn 2) hk
  have hnn := StructuralConsCore.range hZ w (env 3) (env 4) n hw hc
  have hi := SyntaxForestSyntax.intro_inputs 4 w (PureSyntaxTrace.four (env 0) (env 1) k n)
    (fun i => Fin.cases (environmentNat_at w env hn 0) (fun j => Fin.cases (environmentNat_at w env hn 1) (fun l => Fin.cases hkn (fun t => Fin.cases hnn (fun z => Fin.elim0 z) t) l) j) i)
  let B := (Formula.mem (Fin.last m) w.castSucc).conj
    (PureSyntaxTrace.argumentRow w.castSucc (env 0).castSucc (env 1).castSucc k.castSucc n.castSucc (Fin.last m))
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) (SyntaxConstructors.exists_constructor hZ 4 1 w (PureSyntaxTrace.four (env 0) (env 1) k n) hw hi)
  have hZ1 := ZFContext.under hZ B
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw B)
  have hn1 : Derives Δ (environmentNat 5 w.castSucc (fun i => (env i).castSucc)) := of_eq (environmentNat_rename 5 w env Fin.castSucc) (under hn B)
  have hk1 : Derives Δ (successor k.castSucc (env 2).castSucc) := of_eq (successor_rename _ _ Fin.castSucc) (under hk B)
  have hc1 : Derives Δ (StructuralListSyntax.consCode w.castSucc (env 3).castSucc (env 4).castSucc n.castSucc) := of_eq (StructuralListSyntax.consCode_rename _ _ _ _ Fin.castSucc) (under hc B)
  have hp1 : Derives Δ (PureSyntaxTrace.termRow w.castSucc (env 0).castSucc (env 1).castSucc (env 3).castSucc p.castSucc) := of_eq (PureSyntaxTrace.termRow_rename _ _ _ _ _ Fin.castSucc) (under hp B)
  have hq1 : Derives Δ (PureSyntaxTrace.argumentRow w.castSucc (env 0).castSucc (env 1).castSucc (env 2).castSucc (env 4).castSucc q.castSucc) := of_eq (PureSyntaxTrace.argumentRow_rename _ _ _ _ _ _ Fin.castSucc) (under hq B)
  have hcp1 : Derives Δ (PureSyntaxTrace.condition w.castSucc p.castSucc) := of_eq (PureSyntaxTrace.condition_rename w p Fin.castSucc) (under hcp B)
  have hcq1 : Derives Δ (PureSyntaxTrace.condition w.castSucc q.castSucc) := of_eq (PureSyntaxTrace.condition_rename w q Fin.castSucc) (under hcq B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hcond := PureSyntaxConsRule.condition_complete hZ1 _ _ _ _ _ _ _ hw1 hn1 hk1 hc1 (.conjR hB) hp1 hq1 hcp1 hcq1
  exact of_eq (PureSyntaxTrace.arguments_rename w (env 0) (env 1) k n Fin.castSucc).symm
    (PureSyntaxNilComplete.intro_arguments _ _ _ _ _ _ (.conjR hB) hcond)

theorem checked_cons {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w b f ell k h t n : Fin m)
    (hw : Derives Γ (omega w)) (hh : Derives Γ (SyntaxTermSyntax.term w b f h))
    (ht : Derives Γ (SyntaxMixedImageCodeSyntax.termList w ell b f t))
    (hq : Derives Γ (PureSyntaxTrace.arguments w b f ell t))
    (hc : Derives Γ (StructuralListSyntax.consCode w h t n)) (hk : Derives Γ (successor k ell)) :
    Derives Γ (PureSyntaxTrace.arguments w b f k n) := by
  let env : Fin 5 → Fin m := Fin.cases b (Fin.cases f (Fin.cases ell (Fin.cases h (Fin.cases t Fin.elim0))))
  have hhn := SyntaxTerms.range hZ w b f h hw hh
  have htn := Derives.conjL (.conjL (.conjR (.conjR ht)))
  have hen : Derives Γ (environmentNat 5 w env) := HornApplicationRules.intro_nat w env
    (fun i => Fin.cases (.conjL (.conjL hh)) (fun j => Fin.cases (.conjR (.conjL hh)) (fun l => Fin.cases (.conjL ht) (fun v => Fin.cases hhn (fun z => Fin.cases htn (fun x => Fin.elim0 x) z) v) l) j) i)
  have hhead := PureSyntaxTermCorrectness.checked_complete hZ w b f h hw hh
  let P := (PureSyntaxTrace.termRow w.castSucc b.castSucc f.castSucc h.castSucc (Fin.last m)).conj (PureSyntaxTrace.condition w.castSucc (Fin.last m))
  let Δ := Context.add P (Context.image Formula.raise Γ)
  apply Derives.exE (p := P) hhead
  have hP : Derives Δ P := .hyp (Or.inl rfl)
  have hq1 : Derives Δ (PureSyntaxTrace.arguments w.castSucc b.castSucc f.castSucc ell.castSucc t.castSucc) := of_eq (PureSyntaxTrace.arguments_rename _ _ _ _ _ Fin.castSucc) (under hq P)
  let Q := (PureSyntaxTrace.argumentRow w.castSucc.castSucc b.castSucc.castSucc f.castSucc.castSucc ell.castSucc.castSucc t.castSucc.castSucc (Fin.last (m+1))).conj
    (PureSyntaxTrace.condition w.castSucc.castSucc (Fin.last (m+1)))
  let Ξ := Context.add Q (Context.image Formula.raise Δ)
  apply Derives.exE (p := Q) hq1
  have hZ2 := ZFContext.under (ZFContext.under hZ P) Q
  have lift {A : Formula m} (ha : Derives Γ A) : Derives Ξ A.raise.raise := under (under ha P) Q
  have hw2 : Derives Ξ (omega w.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (lift hw)
  have hn2 : Derives Ξ (environmentNat 5 w.castSucc.castSucc (fun i => (env i).castSucc.castSucc)) := of_eq (by simp only [Formula.raise, environmentNat_rename]) (lift hen)
  have hk2 : Derives Ξ (successor k.castSucc.castSucc ell.castSucc.castSucc) := of_eq (by simp only [Formula.raise, successor_rename]) (lift hk)
  have hc2 : Derives Ξ (StructuralListSyntax.consCode w.castSucc.castSucc h.castSucc.castSucc t.castSucc.castSucc n.castSucc.castSucc) := of_eq (by simp only [Formula.raise, StructuralListSyntax.consCode_rename]) (lift hc)
  have hP1 : Derives Ξ ((PureSyntaxTrace.termRow w.castSucc.castSucc b.castSucc.castSucc f.castSucc.castSucc h.castSucc.castSucc (Fin.last m).castSucc).conj (PureSyntaxTrace.condition w.castSucc.castSucc (Fin.last m).castSucc)) := of_eq
    (by simp only [P, Formula.raise, Formula.rename, PureSyntaxTrace.termRow_rename, PureSyntaxTrace.condition_rename]) (under hP Q)
  have hQ : Derives Ξ Q := .hyp (Or.inl rfl)
  have hout := from_rows hZ2 w.castSucc.castSucc k.castSucc.castSucc n.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))
    (fun i => (env i).castSucc.castSucc) hw2 hn2 hk2 hc2 (.conjL hP1) (.conjL hQ) (.conjR hP1) (.conjR hQ)
  exact of_eq (by simp only [Formula.raise, PureSyntaxTrace.arguments_rename]; rfl) hout

end PPAC.Migration.Internal.PureSyntaxConsComplete
