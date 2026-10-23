import PPAC.Migration.Internal.OriginalArgumentProgramFields

/-! 全内部字段像的输出单射性；实际字段见证和项Promise唯一性推出码相等。 -/
namespace PPAC.Migration.Internal.OriginalArgumentFieldUnique
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax
open StructuralListFieldSyntax (field field_rename existsField_rename)
open OriginalArgumentFieldSyntax (fields fields_rename fields_at)
open SyntaxRenameQuerySyntax (of_eq)

theorem term_unique {m} {Γ : Context m} (w mode depth parameter a b c d x y z : Fin m)
    (hp : Derives Γ (OriginalNumericTermValueSyntax.promise w mode depth parameter a b c d))
    (hx : Derives Γ (SyntaxTermSyntax.term w a b x))
    (hy : Derives Γ (OriginalTransformRowSyntax.run 1 w mode depth parameter x y))
    (hz : Derives Γ (OriginalTransformRowSyntax.run 1 w mode depth parameter x z)) : Derives Γ (.equal y z) := by
  have hf := OriginalNumericTermValueSyntax.promise_at w mode depth parameter a b c d x hp hx
  let V := OriginalNumericTermValueSyntax.value w.castSucc mode.castSucc depth.castSucc parameter.castSucc c.castSucc d.castSucc x.castSucc (Fin.last m)
  let Δ := Context.add V (Context.image Formula.raise Γ)
  apply Derives.exE (p := V) hf
  have hy1 : Derives Δ (OriginalTransformRowSyntax.run 1 w.castSucc mode.castSucc depth.castSucc parameter.castSucc x.castSucc y.castSucc) := of_eq (OriginalTransformRowSyntax.run_rename 1 w mode depth parameter x y Fin.castSucc) (under hy V)
  have hz1 : Derives Δ (OriginalTransformRowSyntax.run 1 w.castSucc mode.castSucc depth.castSucc parameter.castSucc x.castSucc z.castSucc) := of_eq (OriginalTransformRowSyntax.run_rename 1 w mode depth parameter x z Fin.castSucc) (under hz V)
  have hV : Derives Δ V := .hyp (Or.inl rfl)
  have heY := OriginalNumericTermValueSyntax.unique _ _ _ _ _ _ _ _ _ hV hy1
  have heZ := OriginalNumericTermValueSyntax.unique _ _ _ _ _ _ _ _ _ hV hz1
  exact eq_trans heY (eq_symm heZ)

theorem field_forward {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w mode depth parameter a b c d k n q r i y : Fin m)
    (hw : Derives Γ (omega w))
    (hL : Derives Γ (SyntaxMixedImageCodeSyntax.termList w k a b n))
    (hp : Derives Γ (OriginalNumericTermValueSyntax.promise w mode depth parameter a b c d))
    (hq : Derives Γ (fields w mode depth parameter k n q))
    (hr : Derives Γ (fields w mode depth parameter k n r))
    (hi : Derives Γ (Formula.mem i k))
    (hy : Derives Γ (field w q i y))
    : Derives Γ (field w r i y) := by
  have hiN := StructuralListTraceOrder.member_member hZ w i k hw (.conjL hL) hi
  have heX := StructuralListFieldValues.exists_value hZ w n i hw hiN
  have heZ := StructuralListFieldValues.exists_value hZ w r i hw hiN
  let X := (Formula.mem (Fin.last m) w.castSucc).conj (field w.castSucc n.castSucc i.castSucc (Fin.last m))
  let Δ := Context.add X (Context.image Formula.raise Γ)
  apply Derives.exE (p := X) heX
  have heZ1 : Derives Δ (StructuralListFieldSyntax.existsField w.castSucc r.castSucc i.castSucc) := of_eq (existsField_rename w r i Fin.castSucc) (under heZ X)
  let Z := (Formula.mem (Fin.last (m+1)) w.castSucc.castSucc).conj (field w.castSucc.castSucc r.castSucc.castSucc i.castSucc.castSucc (Fin.last (m+1)))
  let Ξ := Context.add Z (Context.image Formula.raise Δ)
  apply Derives.exE (p := Z) heZ1
  have hL2 : Derives Ξ (SyntaxMixedImageCodeSyntax.termList w.castSucc.castSucc k.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc n.castSucc.castSucc) := of_eq (by simp only [Formula.raise, SyntaxMixedImageCodeSyntax.termList_rename]) (under (under hL X) Z)
  have hp2 : Derives Ξ (OriginalNumericTermValueSyntax.promise w.castSucc.castSucc mode.castSucc.castSucc depth.castSucc.castSucc parameter.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc) := of_eq (by simp only [Formula.raise, OriginalNumericTermValueSyntax.promise_rename]) (under (under hp X) Z)
  have hq2 : Derives Ξ (fields w.castSucc.castSucc mode.castSucc.castSucc depth.castSucc.castSucc parameter.castSucc.castSucc k.castSucc.castSucc n.castSucc.castSucc q.castSucc.castSucc) := of_eq (by simp only [Formula.raise, fields_rename]) (under (under hq X) Z)
  have hr2 : Derives Ξ (fields w.castSucc.castSucc mode.castSucc.castSucc depth.castSucc.castSucc parameter.castSucc.castSucc k.castSucc.castSucc n.castSucc.castSucc r.castSucc.castSucc) := of_eq (by simp only [Formula.raise, fields_rename]) (under (under hr X) Z)
  have hi2 : Derives Ξ (Formula.mem i.castSucc.castSucc k.castSucc.castSucc) := of_eq (by simp only [Formula.raise, Formula.rename]) (under (under hi X) Z)
  have hy2 : Derives Ξ (field w.castSucc.castSucc q.castSucc.castSucc i.castSucc.castSucc y.castSucc.castSucc) := of_eq (by simp only [Formula.raise, field_rename]) (under (under hy X) Z)
  have hX : Derives Δ X := .hyp (Or.inl rfl)
  have hX2 : Derives Ξ ((Formula.mem (Fin.last m).castSucc w.castSucc.castSucc).conj (field w.castSucc.castSucc n.castSucc.castSucc i.castSucc.castSucc (Fin.last m).castSucc)) := of_eq (by simp only [X, Formula.raise, Formula.rename, field_rename]) (under hX Z)
  have hZval : Derives Ξ Z := .hyp (Or.inl rfl)
  have hTyped := SyntaxMixedImageCodeFields.field_type w.castSucc.castSucc k.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc n.castSucc.castSucc i.castSucc.castSucc (Fin.last m).castSucc hL2 hi2 (.conjR hX2)
  have hRunY := fields_at w.castSucc.castSucc mode.castSucc.castSucc depth.castSucc.castSucc parameter.castSucc.castSucc k.castSucc.castSucc n.castSucc.castSucc q.castSucc.castSucc i.castSucc.castSucc (Fin.last m).castSucc y.castSucc.castSucc hq2 hi2 (.conjR hX2) hy2
  have hRunZ := fields_at w.castSucc.castSucc mode.castSucc.castSucc depth.castSucc.castSucc parameter.castSucc.castSucc k.castSucc.castSucc n.castSucc.castSucc r.castSucc.castSucc i.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) hr2 hi2 (.conjR hX2) (.conjR hZval)
  have he := term_unique w.castSucc.castSucc mode.castSucc.castSucc depth.castSucc.castSucc parameter.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc (Fin.last m).castSucc y.castSucc.castSucc (Fin.last (m+1)) hp2 hTyped hRunY hRunZ
  have ho := StructuralListFieldSyntax.output_subst w.castSucc.castSucc r.castSucc.castSucc i.castSucc.castSucc (Fin.last (m+1)) y.castSucc.castSucc (eq_symm he) (.conjR hZval)
  simpa only [Formula.raise, field_rename] using ho

theorem agree {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w mode depth parameter a b c d k n q r : Fin m)
    (hw : Derives Γ (omega w))
    (hL : Derives Γ (SyntaxMixedImageCodeSyntax.termList w k a b n))
    (hp : Derives Γ (OriginalNumericTermValueSyntax.promise w mode depth parameter a b c d))
    (hq : Derives Γ (fields w mode depth parameter k n q))
    (hr : Derives Γ (fields w mode depth parameter k n r))
    : Derives Γ (StructuralListCodeSyntax.agree w k q r) := by
  apply Derives.allI
  apply Derives.allI
  apply Derives.impI
  let A := Formula.mem (slot 2 0) (old 2 k)
  let Δ := Context.add A (raisedContext 2 Γ)
  have hZ2 := HornBinderRules.zf_body 2 hZ A
  have hw2 : Derives Δ (omega (old 2 w)) := of_eq (by simp only [omega_rename]) (HornBinderRules.under_body 2 hw A)
  have hL2 : Derives Δ (SyntaxMixedImageCodeSyntax.termList (old 2 w) (old 2 k) (old 2 a) (old 2 b) (old 2 n)) := of_eq (by simp only [SyntaxMixedImageCodeSyntax.termList_rename]) (HornBinderRules.under_body 2 hL A)
  have hp2 : Derives Δ (OriginalNumericTermValueSyntax.promise (old 2 w) (old 2 mode) (old 2 depth) (old 2 parameter) (old 2 a) (old 2 b) (old 2 c) (old 2 d)) := of_eq (by simp only [OriginalNumericTermValueSyntax.promise_rename]) (HornBinderRules.under_body 2 hp A)
  have hq2 : Derives Δ (fields (old 2 w) (old 2 mode) (old 2 depth) (old 2 parameter) (old 2 k) (old 2 n) (old 2 q)) := of_eq (by simp only [fields_rename]) (HornBinderRules.under_body 2 hq A)
  have hr2 : Derives Δ (fields (old 2 w) (old 2 mode) (old 2 depth) (old 2 parameter) (old 2 k) (old 2 n) (old 2 r)) := of_eq (by simp only [fields_rename]) (HornBinderRules.under_body 2 hr A)
  apply Derives.conjI
  · apply Derives.impI
    let E := field (old 2 w) (old 2 q) (slot 2 0) (slot 2 1)
    exact field_forward (ZFContext.add hZ2 E) (old 2 w) (old 2 mode) (old 2 depth) (old 2 parameter) (old 2 a) (old 2 b) (old 2 c) (old 2 d) (old 2 k) (old 2 n) (old 2 q) (old 2 r) (slot 2 0) (slot 2 1) (add hw2 E) (add hL2 E) (add hp2 E) (add hq2 E) (add hr2 E) (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))
  · apply Derives.impI
    let E := field (old 2 w) (old 2 r) (slot 2 0) (slot 2 1)
    exact field_forward (ZFContext.add hZ2 E) (old 2 w) (old 2 mode) (old 2 depth) (old 2 parameter) (old 2 a) (old 2 b) (old 2 c) (old 2 d) (old 2 k) (old 2 n) (old 2 r) (old 2 q) (slot 2 0) (slot 2 1) (add hw2 E) (add hL2 E) (add hp2 E) (add hr2 E) (add hq2 E) (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem outputs_unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w mode depth parameter a b c d k n q r : Fin m)
    (hw : Derives Γ (omega w)) (hL : Derives Γ (SyntaxMixedImageCodeSyntax.termList w k a b n))
    (hp : Derives Γ (OriginalNumericTermValueSyntax.promise w mode depth parameter a b c d))
    (hq : Derives Γ (fields w mode depth parameter k n q)) (hr : Derives Γ (fields w mode depth parameter k n r))
    (hQ : Derives Γ (SyntaxMixedImageCodeSyntax.termList w k c d q)) (hR : Derives Γ (SyntaxMixedImageCodeSyntax.termList w k c d r)) : Derives Γ (.equal q r) :=
  StructuralListCodeInduction.unique hZ w k q r hw (.conjR (.conjL (.conjR (.conjR hQ)))) (.conjR (.conjL (.conjR (.conjR hR))))
    (agree hZ w mode depth parameter a b c d k n q r hw hL hp hq hr)

end PPAC.Migration.Internal.OriginalArgumentFieldUnique
