import PPAC.Migration.Internal.PacketHornAffineMatrix

/-! All auxiliary zero/successor/sum values are obtained and discharged inside object quantifiers. -/
namespace PPAC.Migration.Internal.PacketHornAffineLocal
open Source SourceAlgebra SourceLogic OmegaSyntax HornExprSyntax PacketHornAffineSyntax HornBinderSyntax
open SyntaxRenameQuerySyntax (of_eq)
open PacketAffineRuleData (baseRule stepRule radix)

theorem intro_base {m} {Γ : Context m} (wide : Bool) (w B d r z : Fin m)
    (hz : Derives Γ (empty z)) (hr : Derives Γ (row wide w d z d r)) (hd : Derives Γ (.mem d B)) :
    Derives Γ (base wide w B d r) := by
  apply Derives.exI z
  exact of_eq (by simp only [Formula.instantiate, Formula.rename, empty_rename, row_rename,
    Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (.conjI hz (.conjI hr hd))

theorem base_forward {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (wide : Bool) (w B r V : Fin m) (env : Fin 1 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 1 w env))
    (hB : Derives Γ (SyntaxNumeralSyntax.numeral (radix wide) B))
    (hm : Derives Γ (HornRuleSyntax.matrix (baseRule wide) w r V env)) : Derives Γ (base wide w B (env 0) r) := by
  have he := SyntaxNumerals.exists_numeral hZ 0 w hw
  let P := (Formula.mem (Fin.last m) w.castSucc).conj (empty (Fin.last m))
  let Δ := Context.add P (Context.image Formula.raise Γ)
  apply Derives.exE (p := P) he
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw P)
  have hn1 := of_eq (environmentNat_rename 1 w env Fin.castSucc) (under hn P)
  have hB1 := of_eq (SyntaxNumeralSyntax.numeral_rename (radix wide) B Fin.castSucc) (under hB P)
  have hm1 := of_eq (HornRuleSyntax.matrix_rename (baseRule wide) w r V env Fin.castSucc) (under hm P)
  have hP : Derives Δ P := .hyp (Or.inl rfl)
  have ha := Derives.impE (.conjL (PacketHornAffineMatrix.base_at (ZFContext.under hZ P) wide w.castSucc B.castSucc
    (Fin.last m) r.castSucc V.castSucc (fun i => (env i).castSucc) hw1 hn1 hB1 (.conjR hP))) hm1
  exact of_eq (base_rename wide w B (env 0) r Fin.castSucc).symm
    (intro_base wide w.castSucc B.castSucc (env 0).castSucc r.castSucc (Fin.last m) (.conjR hP) (.conjL ha) (.conjR ha))

theorem base_backward {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (wide : Bool) (w B r V : Fin m) (env : Fin 1 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 1 w env))
    (hB : Derives Γ (SyntaxNumeralSyntax.numeral (radix wide) B))
    (hb : Derives Γ (base wide w B (env 0) r)) : Derives Γ (HornRuleSyntax.matrix (baseRule wide) w r V env) := by
  let P := (empty (Fin.last m)).conj
    ((row wide w.castSucc (env 0).castSucc (Fin.last m) (env 0).castSucc r.castSucc).conj (.mem (env 0).castSucc B.castSucc))
  let Δ := Context.add P (Context.image Formula.raise Γ)
  apply Derives.exE (p := P) hb
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw P)
  have hn1 := of_eq (environmentNat_rename 1 w env Fin.castSucc) (under hn P)
  have hB1 := of_eq (SyntaxNumeralSyntax.numeral_rename (radix wide) B Fin.castSucc) (under hB P)
  have hP : Derives Δ P := .hyp (Or.inl rfl)
  exact of_eq (HornRuleSyntax.matrix_rename (baseRule wide) w r V env Fin.castSucc).symm
    (.impE (.conjR (PacketHornAffineMatrix.base_at (ZFContext.under hZ P) wide w.castSucc B.castSucc
      (Fin.last m) r.castSucc V.castSucc (fun i => (env i).castSucc) hw1 hn1 hB1 (.conjL hP))) (.conjR hP))

theorem base_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (wide : Bool) (w B r V : Fin m) (env : Fin 1 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 1 w env))
    (hB : Derives Γ (SyntaxNumeralSyntax.numeral (radix wide) B)) :
    Derives Γ ((HornRuleSyntax.matrix (baseRule wide) w r V env).iff (base wide w B (env 0) r)) := by
  apply Derives.conjI
  · exact .impI (base_forward (ZFContext.add hZ _) wide w B r V env (add hw _) (add hn _) (add hB _) (.hyp (Or.inl rfl)))
  · exact .impI (base_backward (ZFContext.add hZ _) wide w B r V env (add hw _) (add hn _) (add hB _) (.hyp (Or.inl rfl)))

theorem step_forward {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (wide : Bool) (w B r V : Fin m) (env : Fin 3 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 3 w env))
    (hB : Derives Γ (SyntaxNumeralSyntax.numeral (radix wide) B))
    (hm : Derives Γ (HornRuleSyntax.matrix (stepRule wide) w r V env)) :
    Derives Γ (step wide w B V (env 0) (env 1) (env 2) r) := by
  have he := OriginalBinderStepSyntax.successor_exists w (env 1) hw (environmentNat_at w env hn 1)
  let P := (Formula.mem (Fin.last m) w.castSucc).conj (successor (Fin.last m) (env 1).castSucc)
  let Δ := Context.add P (Context.image Formula.raise Γ)
  apply Derives.exE (p := P) he
  have hZ1 := ZFContext.under hZ P
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw P)
  have hn1 := of_eq (environmentNat_rename 3 w env Fin.castSucc) (under hn P)
  have hB1 := of_eq (SyntaxNumeralSyntax.numeral_rename (radix wide) B Fin.castSucc) (under hB P)
  have hm1 := of_eq (HornRuleSyntax.matrix_rename (stepRule wide) w r V env Fin.castSucc) (under hm P)
  have hP : Derives Δ P := .hyp (Or.inl rfl)
  have hy := ZFArithmetic.add_exists hZ1 w.castSucc (env 2).castSucc B.castSucc hw1
    (environmentNat_at w.castSucc (fun i => (env i).castSucc) hn1 2)
    (SyntaxNumerals.range hZ1 (radix wide) w.castSucc B.castSucc hw1 hB1)
  let Q := (Formula.mem (Fin.last (m+1)) w.castSucc.castSucc).conj
    (NaturalAdditionSyntax.sum w.castSucc.castSucc (env 2).castSucc.castSucc B.castSucc.castSucc (Fin.last (m+1)))
  let Ξ := Context.add Q (Context.image Formula.raise Δ)
  apply Derives.exE (p := Q) hy
  have hZ2 := ZFContext.under hZ1 Q
  have hw2 := of_eq (omega_rename w.castSucc Fin.castSucc) (under hw1 Q)
  have hn2 := of_eq (environmentNat_rename 3 w.castSucc (fun i => (env i).castSucc) Fin.castSucc) (under hn1 Q)
  have hB2 := of_eq (SyntaxNumeralSyntax.numeral_rename (radix wide) B.castSucc Fin.castSucc) (under hB1 Q)
  have hm2 := of_eq (HornRuleSyntax.matrix_rename (stepRule wide) w.castSucc r.castSucc V.castSucc (fun i => (env i).castSucc) Fin.castSucc) (under hm1 Q)
  have hP2 : Derives Ξ ((Formula.mem (Fin.last m).castSucc w.castSucc.castSucc).conj
      (successor (Fin.last m).castSucc (env 1).castSucc.castSucc)) := by
    simpa only [P, Formula.raise, Formula.rename, successor_rename] using under hP Q
  have hQ : Derives Ξ Q := .hyp (Or.inl rfl)
  have ha := Derives.impE (.conjL (PacketHornAffineMatrix.step_at hZ2 wide w.castSucc.castSucc B.castSucc.castSucc
    (Fin.last m).castSucc (Fin.last (m+1)) r.castSucc.castSucc V.castSucc.castSucc
    (fun i => (env i).castSucc.castSucc) hw2 hn2 hB2 (.conjR hP2) (.conjR hQ))) hm2
  have hr := intro_step wide w.castSucc.castSucc B.castSucc.castSucc V.castSucc.castSucc
    (env 0).castSucc.castSucc (env 1).castSucc.castSucc (env 2).castSucc.castSucc r.castSucc.castSucc
    (Fin.last m).castSucc (Fin.last (m+1)) (.conjR hP2) (.conjR hQ) (.conjL ha) (.conjR ha)
  simpa only [Formula.raise, step_rename] using hr

theorem step_backward {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (wide : Bool) (w B r V : Fin m) (env : Fin 3 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 3 w env))
    (hB : Derives Γ (SyntaxNumeralSyntax.numeral (radix wide) B))
    (hs : Derives Γ (step wide w B V (env 0) (env 1) (env 2) r)) :
    Derives Γ (HornRuleSyntax.matrix (stepRule wide) w r V env) := by
  let C := stepBody wide w B V (env 0) (env 1) (env 2) r
  let Δ := Context.add C (raisedContext 2 Γ)
  apply HornBinderRules.eliminate_many 2 C _ hs
  have hw2 : Derives Δ (omega (old 2 w)) := of_eq (omega_rename w (old 2)) (HornBinderRules.under_body 2 hw C)
  have hn2 : Derives Δ (environmentNat 3 (old 2 w) (fun i => old 2 (env i))) :=
    of_eq (environmentNat_rename 3 w env (old 2)) (HornBinderRules.under_body 2 hn C)
  have hB2 : Derives Δ (SyntaxNumeralSyntax.numeral (radix wide) (old 2 B)) :=
    of_eq (SyntaxNumeralSyntax.numeral_rename (radix wide) B (old 2)) (HornBinderRules.under_body 2 hB C)
  have hC : Derives Δ C := .hyp (Or.inl rfl)
  exact of_eq (HornRuleSyntax.matrix_rename (stepRule wide) w r V env (old 2)).symm
    (.impE (.conjR (PacketHornAffineMatrix.step_at (HornBinderRules.zf_body 2 hZ C) wide (old 2 w) (old 2 B)
      (slot 2 0) (slot 2 1) (old 2 r) (old 2 V) (fun i => old 2 (env i)) hw2 hn2 hB2
      (.conjL hC) (.conjL (.conjR hC)))) (.conjR (.conjR hC)))

theorem step_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (wide : Bool) (w B r V : Fin m) (env : Fin 3 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 3 w env))
    (hB : Derives Γ (SyntaxNumeralSyntax.numeral (radix wide) B)) :
    Derives Γ ((HornRuleSyntax.matrix (stepRule wide) w r V env).iff (step wide w B V (env 0) (env 1) (env 2) r)) := by
  apply Derives.conjI
  · exact .impI (step_forward (ZFContext.add hZ _) wide w B r V env (add hw _) (add hn _) (add hB _) (.hyp (Or.inl rfl)))
  · exact .impI (step_backward (ZFContext.add hZ _) wide w B r V env (add hw _) (add hn _) (add hB _) (.hyp (Or.inl rfl)))

end PPAC.Migration.Internal.PacketHornAffineLocal
