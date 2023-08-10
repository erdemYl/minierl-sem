erlang_types
=====

An OTP library

Build
-----

    $ rebar3 compile



Roadmap
-----


V 1.0 Basic
===========

* [ ] v1 basic architecture
  * AST test spec defined
  * 2-tuples, intervals
  * generic bdd
  * recursive types via type references
  * hash-consing of types
  * subtyping

Questions

* Are the subtype recursive calls tail-recursive?
  * e.g. `rec_fun() andalso rec_fun2() andalso rec_fun3()` 
  * vs tail-recursive variant


Next
===========
 
* [ ] 2.0 
  * hash-consing of BDD
  * tallying
   
* [ ] 3.0
  * typing ?

* [ ] 4.0 
  * types: arrows, base, atoms
  * 
* [ ] 5.0 
  * types: tuples, functions
  * 
* [ ] 6.0 
  * types: lists, bitstrings, records, specials, ...
