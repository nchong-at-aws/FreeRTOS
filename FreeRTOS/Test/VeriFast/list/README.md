# FreeRTOS list proofs

The list proofs use the following predicates:

  - `ListItem_t` : This predicate captures the well-formedness of a ListItem_t object. `ListItem_t(n, val, next, prev, container)` holds when `n` is of type ListItem_t and has xItemValue `val`, pxNext `next`, pxPrevious `prev`, and pxContainer `container`.

  - `DLS` : DLS is a recursively defined predicate which captures the well-formedness of a segment of a doubly linked-list data-structure. `DLS(n, nprev, mnext, m, cells, container)` holds when the segment in `container` starting from `n` to `m` is a well-formed doubly linked segment and the elements in the segment are `cells`. `nprev` is the pxPrevious field of `n` and `mnext` is the pxNext field of `m`. The base case is when `n` is equal to `m`, in which case `cells` is `cons(n, nil)`. The inductive case is when we have `DLS(nnext, n, mnext, m, cells, container)` and `ListItem_t(n, val, nnext, nprev, container)` and we can conclude `DLS(n, nprev, mnext, m, cons(m, cells), container)`. This predicate is motivated by the DLS predicate in [1].

  - `List_t` : This predicate captures the well-formedness of a List_t object. `ListItem_t(list, len, idx, end, cells)` holds when `list` is of type List_t and has length `len` (not including the xListEnd object), has pxIndex `idx`, xListEnd `end`, and there is a well formed doubly linked list segment with elements `cells` starting from `end`, that is, for some object `endprev`, there exists `DLS(end, endprev, end, endprev, cells, l)`.

  - `List_t_uninitialised` : This predicate captures the shape of a List_t object, without considering its well-formedness. `List_t_uninitialised(list)` holds when `list` is a List_t object and has some value in the field uxNumberOfItems and pxIndex, and xListEnd is a well-formed ListItem_t object.

These predicates are defined in `include/proof/list.h`. 

References:

  1. Ferreira JF, Gherghina C, He G, Qin S, Chin W-N.  2014.  Automated verification of the FreeRTOS scheduler in HIP/SLEEK. International Journal on Software Tools for Technology Transfer. 16(4):381-397.