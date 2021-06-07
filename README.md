# PG3q - Formalizing Finite Projective Spaces PG(3,q)
   
  - checking whether the smallest spaces PG(3,2) and PG(3,3) verify the axioms of projective space geometry. 
  - spreads and packings of PG(3,2) (work in progress)
  
# Authors
Nicolas MAGAUD (magaud@unistra.fr)

# Compilation instructions
  - Coq 8.13.2 (May 2021) (using OCaml 4.12.0 via Opam2)
  - in the directory pg32, generate pg32_inductive.v by running :

    * gcc -o try_pg32 try_pg32.c
    * ./try_pg32 pg32.txt pg32_inductive.v 15 35

- make -f CoqMakefile

# TODO
