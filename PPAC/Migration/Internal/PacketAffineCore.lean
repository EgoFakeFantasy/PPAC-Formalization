import PPAC.Migration.Internal.PacketAffineTransport

/-! Total bounded affine evaluation and scalar uniqueness on all internal natural inputs. -/
namespace PPAC.Migration.Internal.PacketAffineCore
open Source SourceAlgebra SourceLogic OmegaSyntax PacketAffineSyntax ZFArithmetic
open SyntaxRenameQuerySyntax (of_eq)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem radix_guard {m} {Γ : Context m} (w B d t n : Fin m) (ha : Derives Γ (affine w B d t n)) : Derives Γ (.mem B w) := .conjL ha

theorem digit_guard {m} {Γ : Context m} (w B d t n : Fin m) (ha : Derives Γ (affine w B d t n)) : Derives Γ (.mem d B) := .conjL (.conjR ha)

theorem tail_guard {m} {Γ : Context m} (w B d t n : Fin m) (ha : Derives Γ (affine w B d t n)) : Derives Γ (.mem t w) := .conjL (.conjR (.conjR ha))

theorem output_guard {m} {Γ : Context m} (w B d t n : Fin m) (ha : Derives Γ (affine w B d t n)) : Derives Γ (.mem n w) := .conjL (.conjR (.conjR (.conjR ha)))

theorem equation_of_affine {m} {Γ : Context m} (w B d t n : Fin m) (ha : Derives Γ (affine w B d t n)) :
    Derives Γ (equation w B d t n) := .conjR (.conjR (.conjR (.conjR ha)))

theorem digit_natural {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B d t n : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (affine w B d t n)) : Derives Γ (.mem d w) :=
  StructuralListTraceOrder.member_member hZ w d B hw (radix_guard w B d t n ha) (digit_guard w B d t n ha)

theorem exists_value {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B d t : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (.mem B w)) (hd : Derives Γ (.mem d B)) (ht : Derives Γ (.mem t w)) :
    Derives Γ (existsValue w B d t) := by
  have hdN := StructuralListTraceOrder.member_member hZ w d B hw hB hd
  let P := (Formula.mem (Fin.last m) w.castSucc).conj (NaturalMultiplicationSyntax.product w.castSucc B.castSucc t.castSucc (Fin.last m))
  let Ξ := Context.add P (Context.image Formula.raise Γ)
  apply Derives.exE (p := P) (mul_exists hZ w B t hw hB ht)
  have hP : Derives Ξ P := .hyp (Or.inl rfl)
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw P)
  have hd1 : Derives Ξ (.mem d.castSucc w.castSucc) := under hdN P
  have hs := add_exists (ZFContext.under hZ P) w.castSucc d.castSucc (Fin.last m) hw1 hd1 (.conjL hP)
  let N := (Formula.mem (Fin.last (m+1)) w.castSucc.castSucc).conj
    (NaturalAdditionSyntax.sum w.castSucc.castSucc d.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)))
  let Δ := Context.add N (Context.image Formula.raise Ξ)
  apply Derives.exE (p := N) hs
  have hN : Derives Δ N := .hyp (Or.inl rfl)
  have hB2 : Derives Δ (.mem B.castSucc.castSucc w.castSucc.castSucc) := under (under hB P) N
  have hd2 : Derives Δ (.mem d.castSucc.castSucc B.castSucc.castSucc) := under (under hd P) N
  have ht2 : Derives Δ (.mem t.castSucc.castSucc w.castSucc.castSucc) := under (under ht P) N
  have hp2 := of_eq (NaturalMultiplicationSyntax.product_rename w.castSucc B.castSucc t.castSucc (Fin.last m) Fin.castSucc) (under (.conjR hP) N)
  have ha := intro_affine w.castSucc.castSucc B.castSucc.castSucc d.castSucc.castSucc t.castSucc.castSucc (Fin.last (m+1)) (Fin.last m).castSucc
    hB2 hd2 ht2 (.conjL hN) hp2 (.conjR hN)
  exact of_eq (by simp only [Formula.raise, existsValue_rename])
    (intro_exists w.castSucc.castSucc B.castSucc.castSucc d.castSucc.castSucc t.castSucc.castSucc (Fin.last (m+1)) (.conjL hN) ha)

theorem equation_unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B d t n a : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (.mem B w)) (ht : Derives Γ (.mem t w))
    (hn : Derives Γ (equation w B d t n)) (ha : Derives Γ (equation w B d t a)) : Derives Γ (.equal n a) := by
  let P := equationBody w B d t n
  let Ξ := Context.add P (Context.image Formula.raise Γ)
  apply Derives.exE (p := P) hn
  have hP : Derives Ξ P := .hyp (Or.inl rfl)
  have ha1 := of_eq (equation_rename w B d t a Fin.castSucc) (under ha P)
  let Q := equationBody w.castSucc B.castSucc d.castSucc t.castSucc a.castSucc
  let Δ := Context.add Q (Context.image Formula.raise Ξ)
  apply Derives.exE (p := Q) ha1
  have hQ : Derives Δ Q := .hyp (Or.inl rfl)
  have hZ2 := ZFContext.under (ZFContext.under hZ P) Q
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (under (under hw P) Q)
  have hB2 : Derives Δ (.mem B.castSucc.castSucc w.castSucc.castSucc) := under (under hB P) Q
  have ht2 : Derives Δ (.mem t.castSucc.castSucc w.castSucc.castSucc) := under (under ht P) Q
  have hp2 := of_eq (NaturalMultiplicationSyntax.product_rename w.castSucc B.castSucc t.castSucc (Fin.last m) Fin.castSucc) (under (.conjL hP) Q)
  have hs2 := of_eq (NaturalAdditionSyntax.sum_rename w.castSucc d.castSucc (Fin.last m) n.castSucc Fin.castSucc) (under (.conjR hP) Q)
  have he := mul_unique hZ2 w.castSucc.castSucc B.castSucc.castSucc t.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))
    hw2 hB2 ht2 hp2 (.conjL hQ)
  have hpN := mul_range hZ2 w.castSucc.castSucc B.castSucc.castSucc t.castSucc.castSucc (Fin.last m).castSucc hw2 hp2
  have hsQ := PacketAffineTransport.sum_right w.castSucc.castSucc d.castSucc.castSucc (Fin.last (m+1)) a.castSucc.castSucc (Fin.last m).castSucc (eq_symm he) (.conjR hQ)
  exact add_unique hZ2 w.castSucc.castSucc d.castSucc.castSucc (Fin.last m).castSucc n.castSucc.castSucc a.castSucc.castSucc hw2 hpN hs2 hsQ

theorem unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B d t n a : Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (affine w B d t n)) (ha : Derives Γ (affine w B d t a)) : Derives Γ (.equal n a) :=
  equation_unique hZ w B d t n a hw (radix_guard w B d t n hn) (tail_guard w B d t n hn)
    (equation_of_affine w B d t n hn) (equation_of_affine w B d t a ha)

end PPAC.Migration.Internal.PacketAffineCore
