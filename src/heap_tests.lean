/-
Basic tests on the speed of certain sorting algorithms.
The point is to see how fast the binomial_heap and slay_heap
implementations are by testing the speed of their heap sort
algorithms.
-/

import binomial_heap
import splay_heap
import data.list.sort
import init.data.list.qsort

/-- Alternating pos-neg list 
  [-(n-1) (n-1) ... -2 2 -1 1 0 0] 
-/
def build_test_list : ℕ → list ℤ → list ℤ
| 0 l := l
| (nat.succ n) l := -n :: n :: (build_test_list n l)

-- change the number here and uncomment the below lines 
-- to see if they finish or they timeout
def test_size := 100
def long_list := (build_test_list test_size [])
--#eval binomial_heap.heap_reverse_sort (λ m n : ℤ, m ≤ n) long_list
--#eval splay_heap.heap_reverse_sort (λ m n : ℤ, m ≤ n) long_list
--#eval list.insertion_sort (λ m n : ℤ, m ≤ n) long_list
--#eval list.qsort (λ m n : ℤ, m ≤ n) long_list
--#eval list.merge_sort (λ m n : ℤ, m ≤ n) long_list
