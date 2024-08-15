Minimal map semantic subtyping framework
=====

* Type grammar:
   *              t = num | map | t & t | !t
   *              map = { f,...,f, AnyNum => t }
   *              f =  num := t | num => t | name := t | name => t
      * **num** ranges over integers
      * **name** ranges over strings and is meta-theoretic

    
#### Examples
* **{ 1 := 1, alpha := 1, beta => 1 }** specifies maps having
    * key **1** mapped to **1**
    * an unknown *finite* key set, named **alpha**, with each of its keys mapped to **1**
    * an unknown key set, named **beta**, with each of its keys *optionally* mapped to **1**


* **{ alpha := 1, beta := 2 } = { beta := 2, alpha := 1 } = { alphabeta := !(!1 & !2) }**
  * unknown key sets reduce to one unique set
  * reduction by concatenation is chosen for simplicity

#### This framework...
* ...implements semantic subtyping for map types capable of specifying unknown mappings. 
* ...mimics ***the*** subtyping relation of maps where names correspond to type variables.
* ...does ***not*** mimic the subtyping relation of records/maps with row polymorphism.
