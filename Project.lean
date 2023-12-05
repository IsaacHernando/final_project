import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.Init.Data.Int.CompLemmas

open Nat Int List

namespace legendreSym

variable (p : ℕ) [hp : Fact p.Prime]

lemma pos_eq_natAbs {a : ℤ} (h : a > 0) : a = a.natAbs := by
  cases a
  simp only [ofNat_eq_coe, natAbs_ofNat]
  norm_cast at h

@[simp]
lemma legendre_eq_natAbs {a : ℤ} (h : a > 0)
  : legendreSym p a = legendreSym p (natAbs a) := by rw [← pos_eq_natAbs] ; exact h

lemma legendre_neg_mul (h : a ≤ 0) (k : a ≠ 0)
  : legendreSym p a = (legendreSym p (-1)) * (legendreSym p (a.natAbs)) := by
    have : a = -1 * -a := by simp only [mul_neg, neg_mul, one_mul, neg_neg]
    nth_rewrite 1 [this]
    have : -a = (natAbs a) := by simpa using (pos_eq_natAbs (Int.neg_pos_of_neg (Ne.lt_of_le k h)))
    rw [this]
    exact legendreSym.mul p (-1) ↑(natAbs a)

@[simp]
lemma natAbs_legendre_eq_prod_factors {a : ℤ} (h : a ≠ 0)
  : legendreSym p a.natAbs
      = List.prod (a.natAbs.factors.pmap (fun q _ => @legendreSym p _ q) (fun _ _ => hp) ):= by
  nth_rewrite 1 [←  prod_factors (natAbs_ne_zero.mpr h)]
  rw [Lean.Internal.coeM, @bind_pure_comp]
  simp only [map_eq_map, pmap_eq_map, map_map]
  induction (factors (natAbs a))
  case nil => simp only [prod_nil, Nat.cast_one, at_one, map_nil]
  case cons _ _ c =>
    simp only [map_cons, prod_cons, Function.comp_apply]
    rw [←c, ←legendreSym.mul]
    congr

def legendreSym_of_factors_list (a : ℤ) : List ℤ :=
  map (fun a => legendreSym p a) (Lean.Internal.coeM a.natAbs.factors)

def legendreSym_of_reciprocity_map (a : ℤ) : List ℤ :=
  pmap (fun q hq =>
          if q = 2 then legendreSym p 2
          else
            let _ : Fact (Nat.Prime q) := ⟨prime_of_mem_factors hq⟩
            (-1) ^ (q / 2 * (p / 2)) * legendreSym q p) a.natAbs.factors (fun _ x => x)

variable {p : ℕ} [Fact p.Prime] in
lemma factors_list_eq_reciprocity_map (hp' : p ≠ 2)
  : legendreSym_of_factors_list p a = legendreSym_of_reciprocity_map p a := by
      apply List.ext
      intros n
      dsimp only [legendreSym_of_factors_list, legendreSym_of_reciprocity_map]
      simp only [get?_map, Nat.odd_iff_not_even, @get?_pmap, ← @Option.map_eq_map, Option.pmap]
      split
      case a.h_1 _ _ _ _ o _ =>
        simp only [get?_eq_none] at o
        simp only [Lean.Internal.coeM, @bind_pure_comp, map_eq_map, get?_map, Option.map_eq_map,
          Option.map_eq_none', get?_eq_none]
        exact o
      case a.h_2 _ _ _ o₄ o₅ o₆ _ =>
        simp only [Option.map_eq_map, Option.map_eq_some']
        use o₄
        constructor
        ·
          simp only [Lean.Internal.coeM, @bind_pure_comp, map_eq_map, get?_map, Option.map_eq_some']
          exact ⟨o₄, ⟨o₆ ,rfl⟩⟩
        ·
          letI : Fact (Nat.Prime o₄) := ⟨prime_of_mem_factors (o₅ o₄ rfl)⟩
          split_ifs
          case pos h => simp [h]
          case neg h => exact quadratic_reciprocity' h hp'

def legendreAlg_reciprocity (a : ℤ) : ℤ :=
   if _ : a = 0 then 0
   else
      if _ : p = 2 then legendreSym p (a % p)
      else
        if _ : a > 0 then (legendreSym_of_reciprocity_map p a).prod
        else (legendreSym p (-1)) * (legendreSym_of_reciprocity_map p a).prod

@[csimp]
theorem legendreAlg_eq_legendreSym : @legendreSym = @legendreAlg_reciprocity := by
  ext p hp a
  simp only [legendreAlg_reciprocity]
  split_ifs
  case pos h => rw [h] ; simp
  case pos => exact legendreSym.mod p a
  case pos h h' k =>
    rw [←factors_list_eq_reciprocity_map h', legendre_eq_natAbs p k,
      natAbs_legendre_eq_prod_factors p h, pmap_eq_map]
    dsimp [legendreSym_of_factors_list]
  case neg h h' k =>
    simp only [gt_iff_lt, not_lt] at k
    rw [←factors_list_eq_reciprocity_map h', legendre_neg_mul p k h,
      natAbs_legendre_eq_prod_factors, pmap_eq_map]
    congr 1
    assumption
