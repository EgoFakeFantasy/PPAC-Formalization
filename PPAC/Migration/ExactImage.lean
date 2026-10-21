import PPAC.Migration.ReplacementPredicates
import PPAC.Migration.DerivationTransport

/-! 收集界到精确像的逻辑核心。源证书最后可直接编译为原Hilbert核Derives。 -/
namespace PPAC.Migration.ExactImage
open Source ReplacementPredicates SourceLogic

/-- 功能性把一个界内见证扩展为对同一输入的全部输出的界。 -/
theorem bounded_output {n m} {Γ : Context m} (p : Formula (n+2)) (ρ : Fin n → Fin m)
    (x y w : Fin m) (hf : Derives Γ (fiber p ρ x))
    (hb : Derives Γ (boundFiber p ρ w x)) (hxy : Derives Γ (rel p ρ x y)) :
    Derives Γ (.mem y w) := by
  let U : Formula (m+1) := (rel p (paramsUp ρ) x.castSucc (Fin.last m)).conj
    (unique p (paramsUp ρ) x.castSucc (Fin.last m))
  let Γu := Context.add U (Context.image Formula.raise Γ)
  change Derives Γ (.ex U) at hf
  apply Derives.exE (p := U) hf
  change Derives Γu (.mem y.castSucc w.castSucc)
  have hu : Derives Γu (unique p (paramsUp ρ) x.castSucc (Fin.last m)) :=
    .conjR (.hyp (Or.inl rfl))
  have hb' : Derives Γu (boundFiber p (paramsUp ρ) w.castSucc x.castSucc) := by
    simpa only [Formula.raise, boundFiber_rename] using under hb U
  have hxy' : Derives Γu (rel p (paramsUp ρ) x.castSucc y.castSucc) := by
    simpa only [Formula.raise, rel_rename] using under hxy U
  let Z : Formula (m+2) := (Formula.mem (Fin.last (m+1)) w.castSucc.castSucc).conj
    (rel p (paramsUp (paramsUp ρ)) x.castSucc.castSucc (Fin.last (m+1)))
  let Γz := Context.add Z (Context.image Formula.raise Γu)
  change Derives Γu (.ex Z) at hb'
  apply Derives.exE (p := Z) hb'
  change Derives Γz (.mem y.castSucc.castSucc w.castSucc.castSucc)
  have hu' : Derives Γz (unique p (paramsUp (paramsUp ρ)) x.castSucc.castSucc (Fin.last m).castSucc) := by
    simpa only [Formula.raise, unique_rename] using under hu Z
  have hxy'' : Derives Γz (rel p (paramsUp (paramsUp ρ)) x.castSucc.castSucc y.castSucc.castSucc) := by
    simpa only [Formula.raise, rel_rename] using under hxy' Z
  have hz : Derives Γz Z := .hyp (Or.inl rfl)
  have hyu := Derives.impE
    (specialize_unique p (paramsUp (paramsUp ρ)) x.castSucc.castSucc
      (Fin.last m).castSucc y.castSucc.castSucc hu') hxy''
  have hzu := Derives.impE
    (specialize_unique p (paramsUp (paramsUp ρ)) x.castSucc.castSucc
      (Fin.last m).castSucc (Fin.last (m+1)) hu') (Derives.conjR hz)
  exact mem_subst (eq_trans hzu (eq_symm hyu)) (Derives.conjL hz)

/-- 任意关系输出均落在收集界中；没有从存在命题中抽取Lean选择函数。 -/
theorem image_bounded {n m} {Γ : Context m} (p : Formula (n+2)) (ρ : Fin n → Fin m)
    (a w y : Fin m) (ht : Derives Γ (total p ρ a)) (hb : Derives Γ (covered p ρ a w))
    (hi : Derives Γ (image p ρ a y)) : Derives Γ (.mem y w) := by
  let X : Formula (m+1) := (Formula.mem (Fin.last m) a.castSucc).conj
    (rel p (paramsUp ρ) (Fin.last m) y.castSucc)
  let Γx := Context.add X (Context.image Formula.raise Γ)
  change Derives Γ (.ex X) at hi
  apply Derives.exE (p := X) hi
  change Derives Γx (.mem y.castSucc w.castSucc)
  have ht' : Derives Γx (total p (paramsUp ρ) a.castSucc) := by
    simpa only [Formula.raise, total_rename] using under ht X
  have hb' : Derives Γx (covered p (paramsUp ρ) a.castSucc w.castSucc) := by
    simpa only [Formula.raise, covered_rename] using under hb X
  have hx : Derives Γx X := .hyp (Or.inl rfl)
  exact bounded_output p (paramsUp ρ) (Fin.last m) y.castSucc w.castSucc
    (.impE (specialize_total p (paramsUp ρ) a.castSucc (Fin.last m) ht') (.conjL hx))
    (.impE (specialize_covered p (paramsUp ρ) a.castSucc w.castSucc (Fin.last m) hb') (.conjL hx))
    (.conjR hx)

/-- 有界分离结果确实是整个精确像，不只是包含某些已选见证。 -/
theorem exact_image {n m} {Γ : Context m} (p : Formula (n+2)) (ρ : Fin n → Fin m)
    (a w c : Fin m) (ht : Derives Γ (total p ρ a)) (hb : Derives Γ (covered p ρ a w))
    (hs : Derives Γ (separated p ρ a w c)) : Derives Γ (exactImage p ρ a c) := by
  apply Derives.allI
  let Γ' := Context.image Formula.raise Γ
  have ht' : Derives Γ' (total p (paramsUp ρ) a.castSucc) := by
    simpa only [Formula.raise, total_rename] using Derives.rename Fin.castSucc ht
  have hb' : Derives Γ' (covered p (paramsUp ρ) a.castSucc w.castSucc) := by
    simpa only [Formula.raise, covered_rename] using Derives.rename Fin.castSucc hb
  have hs' : Derives Γ' (separated p (paramsUp ρ) a.castSucc w.castSucc c.castSucc) := by
    simpa only [Formula.raise, separated_rename] using Derives.rename Fin.castSucc hs
  have hsep := specialize_separated p (paramsUp ρ) a.castSucc w.castSucc c.castSucc (Fin.last m) hs'
  apply Derives.conjI
  · apply Derives.impI
    exact .conjR (.impE (.conjL (add hsep _)) (.hyp (Or.inl rfl)))
  · apply Derives.impI
    have hI : Derives (Context.add (image p (paramsUp ρ) a.castSucc (Fin.last m)) Γ')
        (image p (paramsUp ρ) a.castSucc (Fin.last m)) := .hyp (Or.inl rfl)
    have hW := image_bounded p (paramsUp ρ) a.castSucc w.castSucc (Fin.last m)
      (add ht' _) (add hb' _) hI
    exact .impE (.conjR (add hsep _)) (.conjI hW hI)
end PPAC.Migration.ExactImage
