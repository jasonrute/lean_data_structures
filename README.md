# Purely functional data structures in Lean
This repository implements some of the data structures from Okasaki's *Purely Functional Data Structures* in [Lean 3](https://leanprover.github.io).  

Also see [Okasaki's thesis by the same title](https://www.cs.cmu.edu/~rwh/theses/okasaki.pdf) which is freely available online.

## Data structures implemented so far and results
- Binomial heap.  Much slower that the splay heap.
- Splay heap.  When used for heap sort, it beats all the other list sorting algorithms in Lean 3 by an order of magnitude, except Lean's `merge_sort` for which it is roughly the same.

## TODO
- [ ] Implement more data structures from the book (or elsewhere).
- [ ] Find more benchmarks (e.g., search algorithms using priority queues). (Is there a way to time code runtime in Lean?)
- [ ] Use Lean to verify that the implementations satisfy the desired properties (e.g. prove that `pop_element` of a heap doesn't change the heap size).