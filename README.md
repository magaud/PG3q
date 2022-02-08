# PG3q - Formalizing Finite Projective Spaces PG(3,q)
   
* Formal implementation of the smallest spaces PG(3,2) and PG(3,3)
* Checking that both PG(3,2) and PG(3,3) verify the axioms of projective space geometry

* Definitions and properties of spreads and packings of PG(3,2)
* Computing all the spreads and packings: there are 56 spreads and 240 packings


* all spreads are isomorphic, i.e. for any 2 spreads S and S', there exists a collineation which maps S onto S'.
* packings can be classified into two distinct classes (each of them featuring 120 elements)
  Showing that these 2 classes are distinct requires to compute all the collineations of PG(3,2) (there are 20160 of them) and check that no collineation allows to map the packing PA0 (which belongs to the first class) onto the packing PA1 (which belongs to the second one). 

# Authors
Nicolas MAGAUD (magaud@unistra.fr)

# Compilation instructions
  - Coq 8.13.2 (October 2021) (using OCaml 4.13.0 via Opam2)
  - PG(3,2): ```make -f CoqMakefile pg32/pg32_packings_two_distinct_classes.vo```
  - PG(3,3): TODO

  - Some parts of the specification are generated automatically (in the directory pg32, you can (re)-generate the files pg32_inductive.v, pg32_automorphisms.v, pg32_automorphisms_inv.v and many others by running the following commands:
```
gcc -o try_pg32 try_pg32.c
./try_pg32 pg32.txt pg32_inductive.v 15 35
gcc -o a automorphisms.c
./a pg32.txt pg32_automorphisms.v 15 35
```


# TODO
- improve automation and compilation time
- exploit symmetries/analogies between statements to solve redundancy issues
- scale to PG(3,3)
