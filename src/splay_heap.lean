import tactic.well_founded_tactics
import tactic.monotonicity

/-
The splay heap from 
Okasaki, Purely Functional Data Structures.
Also see the thesis of the same title with similar code:
https://www.cs.cmu.edu/~rwh/theses/okasaki.pdf.

From the book (p 52):
"Splay trees [...] are the fastest known [purely 
functional] implementation of heaps for most 
applications that do not depend on persistence and 
that do not call the merge function."
-/

namespace splay_heap
section 
  universe variable uu
  parameters {α : Type uu} (r : α → α → Prop) [decidable_rel r]
  local infix ` ≼ ` : 50 := r

  inductive b_tree
  | e : b_tree
  | t (left : b_tree) (middle : α) (right : b_tree) : b_tree

  def empty_tree : b_tree := b_tree.e
  def is_empty_tree : b_tree → bool
  | b_tree.e := tt
  | _ := ff

  /- Note, this is implemented strangly to get around
  the equation compiler which didn't like the mutually
  recursive definition commented out below. -/
  def partition_helper (pivot : α) : b_tree → option (bool × b_tree × b_tree × α) → (b_tree × b_tree)
  | (b_tree.e) (option.none) := (b_tree.e, b_tree.e)
  | t@(b_tree.t a x b) (option.none) :=
    if x ≼ pivot then
      partition_helper b (option.some (ff, a, t, x))
    else
      partition_helper a (option.some (tt, b, t, x))
  | (b_tree.e) (option.some (ff, _, t, _)) := (t, b_tree.e)
  | (b_tree.t b_1 y b_2) (option.some (ff, a, _, x)) :=
    if y ≼ pivot then
      let (small, big) := partition_helper b_2 option.none in
      (b_tree.t (b_tree.t a x b_1) y small, big)
    else
      let (small, big) := partition_helper b_1 option.none in
      (b_tree.t a x small,  b_tree.t big y b_2)
  | (b_tree.e) (option.some (tt, _, t, _)) :=  (b_tree.e, t)
  | (b_tree.t a_1 y a_2) (option.some (tt, b, _, x)) :=
    if y ≼ pivot then
      let (small, big) := partition_helper a_2 option.none in
      (b_tree.t a_1 y small,  b_tree.t big x b)
    else
      let (small, big) := partition_helper a_1 option.none in
      (small, b_tree.t big y (b_tree.t a_2 x b))

  def partition (pivot : α) (t : b_tree) : (b_tree × b_tree) :=
    partition_helper pivot t option.none

  /-mutual def partition, part_left, part_right (pivot : α)
  with partition: b_tree → (b_tree × b_tree)
  | b_tree.e := (b_tree.e, b_tree.e)
  | t@(b_tree.t a x b) :=
    if x ≼ pivot then
      part_left a b x
    else
      part_right a b x
  with part_left : b_tree → b_tree → α → (b_tree × b_tree)
  | a b_tree.e x := (b_tree.t a x b_tree.e, b_tree.e)
  | a (b_tree.t b_1 y b_2) x := 
    if y ≼ pivot then
      let (small, big) := partition b_2 in
      (b_tree.t (b_tree.t a x b_1) y small, big)
    else
      let (small, big) := partition b_1 in
      (b_tree.t a x small,  b_tree.t big y b_2)
  with part_right : b_tree → b_tree → α → (b_tree × b_tree)
  | b_tree.e b x:= (b_tree.e, b_tree.t b_tree.e x b)
  | (b_tree.t a_1 y a_2) b x:= 
    if y ≼ pivot then
      let (small, big) := partition a_2 in
      (b_tree.t a_1 y small,  b_tree.t big x b)
    else
      let (small, big) := partition a_1 in
      (small, b_tree.t big y (b_tree.t a_2 x b))
  using_well_founded wf_tacs
  -/

  def insert_element_tree (t : b_tree) (x : α) :=
    let (a, b) := partition x t in
    b_tree.t a x b

  /-- Note, merge in splay trees is relatively slow. 
  TODO: Get the equation compiler to work so can 
  remove meta.
  -/
  meta def merge_tree : b_tree → b_tree → b_tree
  | b_tree.e t := t 
  | (b_tree.t a x b) t :=
    let (ta, tb) := partition x t in
    b_tree.t (merge_tree ta a) x (merge_tree tb b)

  /- This can be up to O(n).  If calling this and delete,
  then use the combined pop operation.  Otherwise consider
  consider explicitely saving the minimum element. -/
  def find_min_tree : b_tree → option α
  | b_tree.e := option.none
  | (b_tree.t b_tree.e x b) := option.some x
  | (b_tree.t a x b) := find_min_tree a

  def delete_min_tree : b_tree → option b_tree
  | b_tree.e := option.none
  | (b_tree.t b_tree.e x b) := option.some b
  | (b_tree.t (b_tree.t a x b) y c) := 
    match (delete_min_tree a) with
    | option.none := 
      option.some (b_tree.t b y c)
    | (option.some a') := 
      option.some (b_tree.t a' x (b_tree.t b y c))
    end

  def pop_min_tree : b_tree → option (b_tree × α)
  | b_tree.e := option.none
  | (b_tree.t b_tree.e x b) := option.some (b, x)
  | (b_tree.t (b_tree.t a x b) y c) := 
    match (pop_min_tree a) with
    | option.none := 
      option.some (b_tree.t b y c, x)
    | (option.some (a', min)) := 
      option.some (b_tree.t a' x (b_tree.t b y c), min)
    end

  def drain_heap : ℕ -> b_tree → list α → list α
  | 0 _ l := l
  | (nat.succ n) h l := 
    match (pop_min_tree h) with
    | option.none := l
    | option.some (hh, x) := drain_heap n hh (x :: l) 
    end

  def heap_reverse_sort (l : list α) : list α := 
    let n : ℕ := list.length l in
    let t : b_tree := 
      list.foldl insert_element_tree empty_tree l in
    drain_heap n t []
end
end splay_heap