erlang_types
=====

An OTP library

Build
-----

    $ rebar3 compile

 
Open Questions
-----

* Are the subtype recursive calls improved by a tail-recursive variant?
  * e.g. `rec_fun() andalso rec_fun() andalso rec_fun()`
  * vs tail-recursive


Roadmap
-----


* [x] V1 basic architecture
  * AST test spec defined
  * 1-functions, 2-tuples, intervals, atoms
  * generic bdd
  * hash-consing of types
  * subtyping
  * recursive types via type references

* [x] V2
  * tallying
   
* [ ] V3
  * types: n-tuples, n-functions
  * 
* [ ] V4
  * types: named, base, lists, bitstrings, records, specials, maps, ...

* [ ] V_opt1
  * lazy BDDs
  * hash-consing of `ty_rec` operations
  * hash-consing of BDD
  * hash-consing of BDD operations
