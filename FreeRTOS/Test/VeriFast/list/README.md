# FreeRTOS list proofs

In the list proofs we use the following predicates:

  - `ListItem_t` : This predicate captures the well-formedness of a ListItem_t object. `ListItem_t(n, val, next, prev, container)` holds when `n` is of type ListItem_t and has xItemValue `val`, 
  - `DLS` : It is motivated by the DLS predicate in [1].
  - `List_t` :
  - `List_t_uninitialised` :

They are defined in `include/proof/list.h`. 


References:

  1. Ferreira JF, Gherghina C, He G, Qin S, Chin W-N.  2014.  Automated verification of the FreeRTOS scheduler in HIP/SLEEK. International Journal on Software Tools for Technology Transfer. 16(4):381-397.