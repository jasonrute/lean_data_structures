/-
The binomial heap from 
Okasaki, Purely Functional Data Structures.
Also see the thesis of the same title with similar code:
https://www.cs.cmu.edu/~rwh/theses/okasaki.pdf.
-/

namespace binomial_heap
section 
  universe variable uu
  parameters {α : Type uu} (r : α → α → Prop) [decidable_rel r]
  local infix ` ≼ ` : 50 := r

  inductive heap_tree
  | node (rank : ℕ) (element : α ) (subtrees : list heap_tree) 
        : heap_tree

  def rank : heap_tree → ℕ
  | (heap_tree.node n _ _) := n

  def min_element : heap_tree → α 
  | (heap_tree.node _ x _ ) := x

  def subtrees : heap_tree → list heap_tree
  | (heap_tree.node _ _ ts) := ts

  structure binomial_heap := (trees : list heap_tree)

  def empty_heap : binomial_heap := binomial_heap.mk []
  def is_empty (heap: binomial_heap) : bool := heap.trees.empty

  def link (t1 t2: heap_tree) := 
    if (min_element t2 ≼ min_element t1) then 
      heap_tree.node (rank t1 + 1) 
        (min_element t2) (t1 :: (subtrees t2)) 
    else 
      heap_tree.node (rank t1 + 1) 
        (min_element t1) (t2 :: (subtrees t1)) 

  def insert_tree_list : list heap_tree → heap_tree → list heap_tree
    | [] t1 := [t1]
    | l@(t2 :: ts) t1 := 
      if (rank t2 < rank t2) then
        t1 :: l
      else
        insert_tree_list ts (link t1 t2)

  def insert_element (heap: binomial_heap) (x : α) : binomial_heap :=
    let singleton_x := heap_tree.node 0 x [] in
    binomial_heap.mk (insert_tree_list heap.trees singleton_x)

  def merge_list: list heap_tree → list heap_tree → list heap_tree
  | ts [] := ts
  | [] ts := ts
  | l1@(t1 :: ts1) l2@(t2 :: ts2) := 
      if (rank t1 < rank t2) then
        t1 :: merge_list ts1 l2
      else if (rank t2 < rank t1) then
        t2 :: merge_list l1 ts2
      else
        insert_tree_list (merge_list ts1 ts2) (link t1 t2)

  def merge (heap1 heap2 : binomial_heap): binomial_heap :=
    binomial_heap.mk (merge_list heap1.trees heap2.trees)

  def find_min_helper : (list heap_tree) → α → α
    | [] prev_min := prev_min
    | (t :: ts) prev_min := 
      -- on tie take first tree in the heap
      if (prev_min ≼ min_element t) then
        find_min_helper ts prev_min  
      else
        find_min_helper ts (min_element t)
        
  def find_min (heap : binomial_heap) : option α :=
    match heap.trees with
    | [] := option.none
    | (t :: ts) := option.some (find_min_helper ts (min_element t))
    end

  def find_min_tree_index: list heap_tree → ℕ → ℕ → α → ℕ
    | [] _ min_index _ := min_index
    | (t :: ts) n min_index prev_min := 
      -- on tie take first tree in the heap
      if (prev_min ≼ min_element t) then
        find_min_tree_index ts (nat.succ n) min_index prev_min  
      else
        find_min_tree_index ts (nat.succ n) n (min_element t)
  
  def extract_min_tree : list heap_tree → heap_tree → (heap_tree × list heap_tree)
  | [] prev_min_tree := (prev_min_tree, [])
  | l@(t :: ts) prev_min_tree := 
    let (t_min, t_others) := extract_min_tree ts t in
    -- on tie take first tree in the heap
    if (min_element prev_min_tree ≼ min_element t_min) then
      (prev_min_tree, l)
    else
      (t_min, prev_min_tree :: t_others)

  def delete_min (heap : binomial_heap) : option binomial_heap :=
    match heap.trees with
    | [] := option.none
    | (t :: ts) := 
      let (t_min, others) := extract_min_tree ts t in
      option.some (binomial_heap.mk 
        (merge_list (list.reverse (subtrees t_min)) others))
    end

  def pop_min (heap : binomial_heap) : option (binomial_heap × α) :=
    match heap.trees with
    | [] := option.none
    | (t :: ts) := 
      let (t_min, others) := extract_min_tree ts t in
      option.some ((
        (binomial_heap.mk
          (merge_list (list.reverse (subtrees t_min)) others)),
        (min_element t_min)))
    end

  def drain_heap : ℕ -> binomial_heap → list α → list α
  | 0 _ l := l
  | (nat.succ n) h l := 
    match (pop_min h) with
    | option.none := l
    | option.some (hh, x) := drain_heap n hh (x :: l) 
    end

  def heap_reverse_sort (l : list α) : list α := 
    let n : ℕ := list.length l in
    let h : binomial_heap := 
      list.foldl insert_element empty_heap l in
    drain_heap n h []
end
end binomial_heap