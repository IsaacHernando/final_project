import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.Init.Data.Int.CompLemmas
import Mathlib.NumberTheory.LegendreSymbol.ZModChar

open legendreSym Nat Int List ZMod

lemma pos_eq_natAbs {a : ℤ} (h : a ≥ 0) : a = a.natAbs := by
  cases a
  simp only [ofNat_eq_coe, natAbs_ofNat]
  norm_cast at h

lemma legendre_neg_mul (p : ℕ) [hp : Fact p.Prime] (h : a ≤ 0)
  : legendreSym p a = (legendreSym p (-1)) * (legendreSym p (a.natAbs)) := by
    have : a = -1 * -a := by simp only [mul_neg, neg_mul, one_mul, neg_neg]
    nth_rewrite 1 [this]
    have : -a = a.natAbs := by simpa using pos_eq_natAbs (Int.neg_nonneg_of_nonpos h)
    rw [this]
    exact legendreSym.mul p (-1) a.natAbs

lemma natAbs_legendre_eq_prod_factors (p : ℕ) [hp : Fact p.Prime] {a : ℤ} (h : a ≠ 0)
  : legendreSym p a.natAbs
      = List.prod (a.natAbs.factors.pmap (fun q _ => @legendreSym p _ q) (fun _ _ => hp)):= by
  nth_rewrite 1 [←  prod_factors (natAbs_ne_zero.mpr h)]
  rw [Lean.Internal.coeM, @bind_pure_comp]
  simp only [map_eq_map, pmap_eq_map, map_map]
  induction factors (natAbs a)
  case nil => simp only [prod_nil, Nat.cast_one, at_one, map_nil]
  case cons _ _ c =>
    simp only [map_cons, prod_cons, Function.comp_apply]
    rw [←c, ←legendreSym.mul]
    congr

def legendreSym_of_factors_list (p : ℕ) [Fact p.Prime] (a : ℤ) : List ℤ :=
  map (fun a => legendreSym p a) a.natAbs.factors

def legendreSym_of_reciprocity_map (p : ℕ) [Fact p.Prime] (a : ℤ) : List ℤ :=
  pmap (fun q hq =>
          if q = 2 then χ₈ p
          else
            let _ : Fact (Nat.Prime q) := ⟨prime_of_mem_factors hq⟩
            (-1) ^ (q / 2 * (p / 2)) * legendreSym q p) a.natAbs.factors (fun _ x => x)

variable {p : ℕ} [Fact p.Prime] in
lemma factors_list_eq_reciprocity_map (a : ℤ) (hp' : p ≠ 2)
  : legendreSym_of_factors_list p a = legendreSym_of_reciprocity_map p a := by
      apply List.ext
      intros n
      dsimp only [legendreSym_of_factors_list, legendreSym_of_reciprocity_map]
      simp only [get?_map, Nat.odd_iff_not_even, @get?_pmap, ← @Option.map_eq_map, Option.pmap]
      split
      case a.h_1 _ _ _ _ o _ =>
        simp only [Lean.Internal.coeM, @bind_pure_comp, map_eq_map, get?_map, Option.map_eq_map,
          Option.map_eq_none', get?_eq_none]
        simpa only [get?_eq_none] using o
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
          case pos h => rw [h] ; exact legendreSym.at_two hp'
          case neg h => exact quadratic_reciprocity' h hp'

def reciprocity_recursion (p : ℕ) [hp : Fact p.Prime] (a : ℕ) : ℤ :=
    if _ : a = 0 then 0
    else if _ : p = 2 then legendreSym p (a % p)
    else List.prod <|
      pmap (fun q hq =>
            if _ : q = 2 then χ₈ p
            else
              let _ : Fact (Nat.Prime q) := ⟨prime_of_mem_factors hq⟩
              (-1) ^ (q / 2 * (p / 2)) * reciprocity_recursion q (p % q)) a.factors (fun _ x => x)
termination_by
  reciprocity_recursion p a => a
decreasing_by
  simp_wf
  exact Nat.lt_of_lt_of_le (mod_lt p Fin.size_pos') (le_of_mem_factors hq)

lemma reciprocity_recursion_eq_legendreSym (p : ℕ) [hp : Fact p.Prime] (a : ℕ) :
  reciprocity_recursion p a = legendreSym p a := by
    unfold reciprocity_recursion
    split_ifs
    case pos h => rw [h] ; simp
    case pos => rw [← legendreSym.mod]
    case neg h1 h2 =>
      rw [pos_eq_natAbs ((ofNat_nonneg a)),
        natAbs_legendre_eq_prod_factors p (a := (a : ℤ)) (ofNat_ne_zero.mpr h1)]
      simp only [pmap_eq_map]
      change _ = (legendreSym_of_factors_list p a).prod
      rw [factors_list_eq_reciprocity_map, legendreSym_of_reciprocity_map]
      congr ; ext x hx ; congr ; ext ; congr
      letI : Fact x.Prime := ⟨prime_of_mem_factors hx⟩
      rw [legendreSym.mod x]
      exact reciprocity_recursion_eq_legendreSym x (p % x)
      assumption
termination_by _ p hp a => a
decreasing_by
  simp_wf
  apply Nat.lt_of_lt_of_le (mod_lt p (pos_of_mem_factors hx)) (le_of_mem_factors hx)

def reciprocity_recursion' (p : ℕ) [Fact p.Prime] (a : ℤ) : ℤ :=
  if _ : p = 2 then legendreSym p (a % p)
  else if _ : a < 0 then (χ₄ p) * (reciprocity_recursion p a.natAbs)
  else (reciprocity_recursion p a.natAbs)

@[csimp]
lemma reciprocity_recursion_eq_legendreSym' :
  @reciprocity_recursion' = @legendreSym := by
    ext p hp a
    dsimp only [reciprocity_recursion']
    split_ifs
    case pos => rw [← legendreSym.mod]
    case pos h h' =>
      rw [legendre_neg_mul p (Int.le_of_lt h'), at_neg_one h, reciprocity_recursion_eq_legendreSym]
    case neg h =>
      symm
      nth_rewrite 1 [pos_eq_natAbs (Int.not_lt.mp h)]
      rw [reciprocity_recursion_eq_legendreSym]

-- def legendre_reciprocity (p : ℕ) [Fact p.Prime] (a : ℤ) : ℤ :=
--    if _ : a = 0 then 0
--    else if _ : p = 2 then legendreSym p (a % p)
--    else if _ : a > 0 then (legendreSym_of_reciprocity_map p a).prod
--    else (χ₄ p) * (legendreSym_of_reciprocity_map p a).prod

-- @[csimp]
-- theorem legendreSym_eq_legendre_reciprocity : @legendreSym = @legendre_reciprocity := by
--   ext p hp a
--   simp only [legendre_reciprocity]
--   split_ifs
--   case pos h => rw [h, at_zero]
--   case pos => exact legendreSym.mod p a
--   case pos h h' k =>
--     rw [←factors_list_eq_reciprocity_map,
--       pos_eq_natAbs (Int.nonneg_of_pos k), natAbs_legendre_eq_prod_factors p h, pmap_eq_map]
--     dsimp [legendreSym_of_factors_list]
--     assumption
--   case neg h h' k =>
--     simp only [gt_iff_lt, not_lt] at k
--     rw [←factors_list_eq_reciprocity_map, legendre_neg_mul p,
--       natAbs_legendre_eq_prod_factors, pmap_eq_map, legendreSym.at_neg_one h']
--     congr 1
--     assumption'
