# PG3X - A Coq Formalisation of Finite Projective Spaces PG(3,q) with q=2,3. 


# Authors


# Compilation instructions
  - coq 8.12.2 (using Ocaml 4.11.1 via Opam2)
  - in the directory pg32, generate pg32_inductive.v by running :

    * gcc -o try_pg32 try_pg32.c
    * ./try_pg32 pg32.txt pg32_inductive.v 15 35

- make -f CoqMakefile
