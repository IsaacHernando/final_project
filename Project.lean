import Project.Basic
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.Tactic
import Mathlib.Init.Data.Int.CompLemmas

open ZMod legendreSym Nat Int List

variable (a : ℤ)

example (h : a < 0) : -a > 0 := by exact Int.neg_pos_of_neg h

lemma pos_eq_natAbs (h : a > 0) : a = a.natAbs := by
  cases a
  simp only [ofNat_eq_coe, natAbs_ofNat]
  case negSucc h' => norm_cast

lemma neg_mul_eq_natAbs (h : a < 0) : -a = a.natAbs := by
  have := pos_eq_natAbs (-a) (Int.neg_pos_of_neg h)
  norm_cast at this
  simp at this
  norm_cast

lemma list_prod_eq_int_pos (h: a > 0) : List.prod (factors (natAbs a)) = a := by
  nth_rewrite 2 [pos_eq_natAbs a]
  norm_cast
  apply prod_factors
  simp only [ne_eq, natAbs_eq_zero]
  exact Int.ne_of_gt h
  assumption

lemma list_prod_eq_int_neg (h: a < 0) : List.prod (factors (natAbs a)) = -a := by
  have : natAbs a = natAbs (-a) := by simp
  rw [this]
  have aa := pos_eq_natAbs (-a) (Int.neg_pos_of_neg h)
  norm_cast at aa
  simp at aa
  have : -a = (natAbs a) := by norm_cast
  apply list_prod_eq_int_pos
  simp only [gt_iff_lt, Left.neg_pos_iff]
  assumption

lemma list_prod_eq_int_neg' (h : a < 0) : (-1) * List.prod (factors (natAbs a)) = a := by
  rw [list_prod_eq_int_neg]
  simp only [mul_neg, neg_mul, one_mul, neg_neg]
  assumption

lemma pos_int_is_nat (h : a > 0) : a.toNat = a := toNat_of_nonneg (Int.nonneg_of_pos h)

variable (p : ℕ) [hp : Fact p.Prime] (a : ℤ)

lemma legendre_neg_mul : legendreSym p a = (legendreSym p (-1)) * (legendreSym p (-a)) := by
  have : a = -1 * -a := by simp only [mul_neg, neg_mul, one_mul, neg_neg]
  nth_rewrite 1 [this]
  exact legendreSym.mul p (-1) (-a)

lemma legendre_neg_mul' (h : a < 0) : legendreSym p a = (legendreSym p (-1)) * (legendreSym p (a.natAbs)) := by
  have : a = -1 * -a := by simp only [mul_neg, neg_mul, one_mul, neg_neg]
  nth_rewrite 1 [this]
  have : natAbs a = natAbs (-a) := by simp
  have aa := pos_eq_natAbs (-a) (Int.neg_pos_of_neg h)
  norm_cast at aa
  simp at aa
  have : -a = (natAbs a) := by norm_cast
  rw [this]
  apply legendreSym.mul

lemma legendre_factorization_pos (h : a > 0) : legendreSym p a = legendreSym p (List.prod (factors a.natAbs)) := by
  have := list_prod_eq_int_pos a h
  norm_cast at this
  nth_rewrite 1 [←this]
  rw [Lean.Internal.coeM, @bind_pure_comp]
  rfl

lemma legendre_factorization_neg (h : a < 0)
  : legendreSym p a = (legendreSym p (-1)) * legendreSym p (List.prod (factors a.natAbs)) := by
    rw [legendre_neg_mul']
    congr 1
    · nth_rewrite 1 [legendre_factorization_pos]
      norm_cast ; norm_cast
      have := neg_mul_eq_natAbs a h
      have h' : -a > 0 := by exact Int.neg_pos_of_neg h
      rw [this] at h'
      norm_cast at h'
    · assumption

lemma factorization_eq_prod_factorization_pos (h : a > 0): (legendreSym p a) = List.prod ( a.natAbs.factors.pmap (fun q _ => @legendreSym p hp  q) (fun _ _ => hp) ):= by
  rw [legendre_factorization_pos, Lean.Internal.coeM, @bind_pure_comp]
  simp only [map_eq_map, pmap_eq_map, map_map]
  induction (factors (natAbs a))
  case nil => simp only [map_nil, prod_nil, at_one]
  case cons => simp only [map_cons, prod_cons, Function.comp_apply, legendreSym.mul] ; congr 1
  assumption

lemma factorization_eq_prod_factorization_neg (h : a < 0): (legendreSym p a) = (legendreSym p (-1)) * List.prod ( a.natAbs.factors.pmap (fun q _ => @legendreSym p hp q) (fun _ _ => hp) ):= by
  rw [legendre_neg_mul]
  congr 1
  rw [neg_mul_eq_natAbs]
  case e_a =>
    have hh := factorization_eq_prod_factorization_pos p (natAbs a) (by simp ; exact Int.ne_of_lt h)
    rw [hh]
    norm_cast
  assumption

-- def legendreAlg_reciprocity : ℤ :=
--    if _ : a = 0 then 0
--    else
--        if h₁ : p = 2 then legendreSym p (a % p)
--        else
--           if _ : a > 0 then
--               List.prod <|
--                 (natAbs a).factors.pmap
--                     (fun q hq' =>
--                         if h₂ : q = 2 then legendreSym p 2
--                         else
--                           quadratic_reciprocity' h₁ h₂)
--                     (fun b hq' _ _ => by {

--                     })
--           else ((natAbs a).factors.pmap
--                   (fun q _ => (-1) ^ (p / 2 * (q / 2)) * legendreSym p q)
--                   (fun _ _ => fact_iff.mp hp)).prod
--                     * legendreSym p (-1)


def legendreAlg_reciprocity : ℤ :=
   if _ : a = 0 then 0
   else
       if _ : p = 2 then legendreSym p (a % p)
       else
          if _ : a > 0 then
              List.prod <|
                   let f := fun (q : ℕ) (_ : Fact q.Prime) =>
                      if _ : q = 2 then legendreSym p 2
                      else (-1) ^ (p / 2 * (q / 2)) * legendreSym q p
                   (natAbs a).factors.pmap f (fun _ hq => ⟨prime_of_mem_factors hq ⟩)
          else
              (legendreSym p (-1)) *
              (List.prod <|
                   let f := fun (q : ℕ) (_ : Fact q.Prime) =>
                      if _ : q = 2 then legendreSym p 2
                      else (-1) ^ (p / 2 * (q / 2)) * legendreSym q p
                   (natAbs a).factors.pmap f (fun _ hq => ⟨prime_of_mem_factors hq ⟩))

-- @[csimp]
-- theorem legendreAlg_eq_legendreSym : @legendreSym = @legendreAlg_reciprocity := by {
--   ext p hp a
--   dsimp only [legendreAlg_reciprocity]
--   split_ifs
--   case pos h => simp [h]
--   case pos h h'=> exact legendreSym.mod p a
--   case neg h h' h'' => {
--     simp
--     have : a = (-1) * (-a) := by simp
--     nth_rewrite 1 [this]
--     rw [legendreSym.mul]
--     congr 1
--     rw [@pmap_eq_map_attach]


--   }
-- }
