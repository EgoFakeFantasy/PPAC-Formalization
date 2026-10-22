import PPAC.Migration.Internal.SyntaxTermImagePrefixGraph

/-! 混合binder新头部的实际原bvar0码和合法目标项；空集与项码均在对象量词内取得。 -/
namespace PPAC.Migration.Internal.SyntaxMixedImageHead
open Source SourceAlgebra SourceLogic OmegaSyntax SyntaxRenameQuerySyntax

def head {m} (w C d z n : Fin m) : Formula m := (empty z).conj
  ((SyntaxVariableSyntax.code true w z n).conj (SyntaxTermSyntax.term w C d n))

def codeExists {m} (w C d z : Fin m) : Formula m := .ex
  (head w.castSucc C.castSucc d.castSucc z.castSucc (Fin.last m))

def existsHead {m} (w C d : Fin m) : Formula m := .ex
  (codeExists w.castSucc C.castSucc d.castSucc (Fin.last m))

theorem head_rename {m k} (w C d z n : Fin m) (ρ : Fin m → Fin k) :
    (head w C d z n).rename ρ = head (ρ w) (ρ C) (ρ d) (ρ z) (ρ n) := by
  simp only [head, Formula.rename, empty_rename, SyntaxVariableSyntax.code_rename, SyntaxTermSyntax.term_rename]

theorem codeExists_rename {m k} (w C d z : Fin m) (ρ : Fin m → Fin k) :
    (codeExists w C d z).rename ρ = codeExists (ρ w) (ρ C) (ρ d) (ρ z) := by
  simp only [codeExists, Formula.rename, head_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem existsHead_rename {m k} (w C d : Fin m) (ρ : Fin m → Fin k) :
    (existsHead w C d).rename ρ = existsHead (ρ w) (ρ C) (ρ d) := by
  simp only [existsHead, Formula.rename, codeExists_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem term_at_zero {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w c C d z n : Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (.mem c w)) (hd : Derives Γ (.mem d w))
    (hC : Derives Γ (successor C c)) (hz : Derives Γ (empty z)) (hn : Derives Γ (SyntaxVariableSyntax.code true w z n)) :
    Derives Γ (SyntaxTermSyntax.term w C d n) := by
  have hCNat := OmegaStructureAlgebra.successor_member w C c (ZFContext.arithmetic hZ).base.extensionality hw hc hC
  have hzC := SyntaxIndexLiftOrder.zero_member hZ w c C z hw hc hC hz
  exact SyntaxTermSyntax.intro_term true w C d n z (.conjI (.conjI hCNat hd) hzC) hn

theorem code_exists {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w c C d z : Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (.mem c w)) (hd : Derives Γ (.mem d w))
    (hC : Derives Γ (successor C c)) (hz : Derives Γ (empty z)) : Derives Γ (codeExists w C d z) := by
  have hzNat := OmegaStructureAlgebra.zero_member w z (ZFContext.arithmetic hZ).base.extensionality hw hz
  let N := (Formula.mem (Fin.last m) w.castSucc).conj (SyntaxVariableSyntax.code true w.castSucc z.castSucc (Fin.last m))
  let Δ := Context.add N (Context.image Formula.raise Γ)
  apply Derives.exE (p := N) (SyntaxVariables.exists_code hZ true w z hw hzNat)
  have hZ1 := ZFContext.under hZ N
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw N)
  have hC1 : Derives Δ (successor C.castSucc c.castSucc) := of_eq (successor_rename C c Fin.castSucc) (under hC N)
  have hz1 : Derives Δ (empty z.castSucc) := of_eq (empty_rename z Fin.castSucc) (under hz N)
  have hN : Derives Δ N := .hyp (Or.inl rfl)
  have ht := term_at_zero hZ1 _ _ _ _ _ _ hw1 (under hc N) (under hd N) hC1 hz1 (.conjR hN)
  have hh : Derives Δ (head w.castSucc C.castSucc d.castSucc z.castSucc (Fin.last m)) := .conjI hz1 (.conjI (.conjR hN) ht)
  have ho : Derives Δ (codeExists w.castSucc C.castSucc d.castSucc z.castSucc) := by
    apply Derives.exI (Fin.last m)
    exact of_eq (by simp only [Formula.instantiate, head_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hh
  exact of_eq (codeExists_rename w C d z Fin.castSucc).symm ho

theorem exists_head {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w c C d : Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (.mem c w)) (hd : Derives Γ (.mem d w))
    (hC : Derives Γ (successor C c)) : Derives Γ (existsHead w C d) := by
  have he : Derives Γ (Source.SetLanguage.emptySet.rename Fin.elim0) := .hyp (hZ _ ⟨_, Source.SetLanguage.IsZFAxiom.emptySet, rfl⟩)
  let Z := empty (Fin.last m)
  let Δ := Context.add Z (Context.image Formula.raise Γ)
  apply Derives.exE (p := Z) (ObjectTransitiveCover.empty_exists_at he)
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw Z)
  have hC1 : Derives Δ (successor C.castSucc c.castSucc) := of_eq (successor_rename C c Fin.castSucc) (under hC Z)
  have hn := code_exists (ZFContext.under hZ Z) _ _ _ _ _ hw1 (under hc Z) (under hd Z) hC1 (.hyp (Or.inl rfl))
  have ho : Derives Δ (existsHead w.castSucc C.castSucc d.castSucc) := by
    apply Derives.exI (Fin.last m)
    exact of_eq (by simp only [Formula.instantiate, codeExists_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hn
  exact of_eq (existsHead_rename w C d Fin.castSucc).symm ho

end PPAC.Migration.Internal.SyntaxMixedImageHead
