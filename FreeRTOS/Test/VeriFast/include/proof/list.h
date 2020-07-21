/*
 * FreeRTOS VeriFast Proofs
 * Copyright (C) Amazon.com, Inc. or its affiliates.  All Rights Reserved.
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy of
 * this software and associated documentation files (the "Software"), to deal in
 * the Software without restriction, including without limitation the rights to
 * use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of
 * the Software, and to permit persons to whom the Software is furnished to do so,
 * subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
 * FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
 * COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER
 * IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
 * CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 */


#ifndef LIST_H
#define LIST_H

#define VERIFAST
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <threading.h>

typedef int TickType_t;
typedef int UBaseType_t;
typedef int BaseType_t;

// Macros:

#define listFIRST_LIST_ITEM_INTEGRITY_CHECK_VALUE
#define listSECOND_LIST_ITEM_INTEGRITY_CHECK_VALUE
#define listFIRST_LIST_INTEGRITY_CHECK_VALUE
#define listSECOND_LIST_INTEGRITY_CHECK_VALUE
#define configLIST_VOLATILE
#define PRIVILEGED_FUNCTION
#define mtCOVERAGE_TEST_DELAY();
#define mtCOVERAGE_TEST_MARKER();
#define listSET_FIRST_LIST_ITEM_INTEGRITY_CHECK_VALUE( pxItem )
#define listSET_SECOND_LIST_ITEM_INTEGRITY_CHECK_VALUE( pxItem )
#define listSET_LIST_INTEGRITY_CHECK_1_VALUE( pxList )
#define listSET_LIST_INTEGRITY_CHECK_2_VALUE( pxList )
#define listTEST_LIST_ITEM_INTEGRITY( pxItem )
#define listTEST_LIST_INTEGRITY( pxList )
#define portMAX_DELAY 127

// Objects:

struct xLIST;
struct xLIST_ITEM
{
listFIRST_LIST_ITEM_INTEGRITY_CHECK_VALUE           /*< Set to a known value if configUSE_LIST_DATA_INTEGRITY_CHECK_BYTES is set to 1. */
    int xItemValue;          /*< The value being listed.  In most cases this is used to sort the list in descending order. */
    struct xLIST_ITEM * configLIST_VOLATILE pxNext;     /*< Pointer to the next ListItem_t in the list. */
    struct xLIST_ITEM * configLIST_VOLATILE pxPrevious; /*< Pointer to the previous ListItem_t in the list. */
    void * pvOwner;                                     /*< Pointer to the object (normally a TCB) that contains the list item.  There is therefore a two way link between the object containing the list item and the list item itself. */
    struct xLIST * configLIST_VOLATILE pxContainer;     /*< Pointer to the list in which this list item is placed (if any). */
    listSECOND_LIST_ITEM_INTEGRITY_CHECK_VALUE          /*< Set to a known value if configUSE_LIST_DATA_INTEGRITY_CHECK_BYTES is set to 1. */
};
typedef struct xLIST_ITEM ListItem_t;                   /* For some reason lint wants this as two separate definitions. */

  struct xMINI_LIST_ITEM
  {
    listFIRST_LIST_ITEM_INTEGRITY_CHECK_VALUE /*< Set to a known value if configUSE_LIST_DATA_INTEGRITY_CHECK_BYTES is set to 1. */
    configLIST_VOLATILE TickType_t xItemValue;
    struct xLIST_ITEM * configLIST_VOLATILE pxNext;
    struct xLIST_ITEM * configLIST_VOLATILE pxPrevious;
  };
  typedef struct xMINI_LIST_ITEM MiniListItem_t;

typedef struct xLIST
{
    listFIRST_LIST_INTEGRITY_CHECK_VALUE      /*< Set to a known value if configUSE_LIST_DATA_INTEGRITY_CHECK_BYTES is set to 1. */
    volatile UBaseType_t uxNumberOfItems;
    ListItem_t * configLIST_VOLATILE pxIndex; /*< Used to walk through the list.  Points to the last item returned by a call to listGET_OWNER_OF_NEXT_ENTRY (). */
    ListItem_t xListEnd;                  /*< List item that contains the maximum possible item value meaning it is always at the end of the list and is therefore used as a marker. */
    listSECOND_LIST_INTEGRITY_CHECK_VALUE     /*< Set to a known value if configUSE_LIST_DATA_INTEGRITY_CHECK_BYTES is set to 1. */
} List_t;

#define listSET_LIST_ITEM_OWNER( pxListItem, pxOwner )    ( ( pxListItem )->pvOwner = ( void * ) ( pxOwner ) )
#define listGET_LIST_ITEM_OWNER( pxListItem )             ( ( pxListItem )->pvOwner )
#define listSET_LIST_ITEM_VALUE( pxListItem, xValue )     ( ( pxListItem )->xItemValue = ( xValue ) )
#define listGET_LIST_ITEM_VALUE( pxListItem )             ( ( pxListItem )->xItemValue )
#define listGET_ITEM_VALUE_OF_HEAD_ENTRY( pxList )        ( ( ( pxList )->xListEnd ).pxNext->xItemValue )
#define listGET_HEAD_ENTRY( pxList )                      ( ( ( pxList )->xListEnd ).pxNext )
#define listGET_NEXT( pxListItem )                        ( ( pxListItem )->pxNext )
#define listGET_END_MARKER( pxList )                      ( ( ListItem_t const * ) ( &( ( pxList )->xListEnd ) ) )
#define listLIST_IS_EMPTY( pxList )                       ( ( ( pxList )->uxNumberOfItems == ( UBaseType_t ) 0 ) ? pdTRUE : pdFALSE )
#define listCURRENT_LIST_LENGTH( pxList )                 ( ( pxList )->uxNumberOfItems )
#define listGET_OWNER_OF_NEXT_ENTRY( pxTCB, pxList )                                       \
{                                                                                          \
    List_t * const pxConstList = ( pxList );                                               \
    /* Increment the index to the next item and return the item, ensuring */               \
    /* we don't return the marker used at the end of the list.  */                         \
    ( pxConstList )->pxIndex = ( pxConstList )->pxIndex->pxNext;                           \
    if( ( void * ) ( pxConstList )->pxIndex == ( void * ) &( ( pxConstList )->xListEnd ) ) \
    {                                                                                      \
        ( pxConstList )->pxIndex = ( pxConstList )->pxIndex->pxNext;                       \
    }                                                                                      \
    ( pxTCB ) = ( pxConstList )->pxIndex->pvOwner;                                         \
}
#define listGET_OWNER_OF_HEAD_ENTRY( pxList )            ( ( &( ( pxList )->xListEnd ) )->pxNext->pvOwner )
#define listIS_CONTAINED_WITHIN( pxList, pxListItem )    ( ( ( pxListItem )->pxContainer == ( pxList ) ) ? ( pdTRUE ) : ( pdFALSE ) )
#define listLIST_ITEM_CONTAINER( pxListItem )            ( ( pxListItem )->pxContainer )
#define listLIST_IS_INITIALISED( pxList )                ( ( pxList )->xListEnd.xItemValue == portMAX_DELAY )

/*@

predicate ListItem_t(
  struct xLIST_ITEM *n,
  unsigned char val,
  struct xLIST_ITEM *next,
  struct xLIST_ITEM *prev,
  struct xLIST *container) =
  n->xItemValue |-> val &*&
  n->pxNext |-> next &*&
  n->pxPrevious |-> prev &*&
  n->pxContainer |-> container;

predicate disjoint<t>(list<t> l1, list<t> l2) =
  (l1 == nil)? true : l1 == cons(?h1, ?t1) &*& (mem(h1, t1) == false) &*& disjoint(t1, l2);
  
predicate DLS(
  struct xLIST_ITEM *n,
  struct xLIST_ITEM *nprev,
  struct xLIST_ITEM *mnext,
  struct xLIST_ITEM *m,
  list<struct xLIST_ITEM *> cells) =
  n == m ? cells == cons(n, nil) &*&
           ListItem_t(n, _, mnext, nprev, _)
         : cells == cons(n, ?cells0) &*&
           ListItem_t(n, _, ?o, nprev, _) &*& 
           DLS(o, n, mnext, m, cells0);

predicate List_t(
  struct xLIST *l,
  int len,
  struct xLIST_ITEM *idx,
  struct xLIST_ITEM *end,
  list<struct xLIST_ITEM *>cells) =
  l->uxNumberOfItems |-> len &*&
  l->pxIndex |-> idx &*&
  end == &(l->xListEnd) &*&
  end == head(cells) &*&
  len + 1 == length(cells) &*&
  len >= 0 &*&
  mem(idx, cells) == true &*&
  DLS(end, ?m, end, m, cells);
  
predicate List_t_uninitialised(struct xLIST *list) = 
    list->uxNumberOfItems |-> _ &*&
    list->pxIndex |-> _ &*&
    ListItem_t(&(list->xListEnd), _, _, _, _);

@*/


void vListInitialise( List_t * const pxList ) PRIVILEGED_FUNCTION;
    //@ requires List_t_uninitialised(pxList); 
    //@ ensures List_t(pxList, 0, ?end, end, cons(end,nil));

    void vListInitialiseItem( ListItem_t * const pxItem ) PRIVILEGED_FUNCTION;
    //@ requires ListItem_t(pxItem, ?value, ?next, ?prev, _);
    //@ ensures ListItem_t(pxItem, value, next, prev, NULL);

    void vListInsert( List_t * const pxList,
                      ListItem_t * const pxNewListItem ) PRIVILEGED_FUNCTION;


    void vListInsertEnd( List_t * const pxList,
                         ListItem_t * const pxNewListItem ) PRIVILEGED_FUNCTION;
    //@ requires List_t(pxList, ?len, ?idx, ?end, ?cells) &*& ListItem_t(pxNewListItem, ?val, _, _, _) &*& (mem(pxNewListItem, cells) == false);
    //@ ensures List_t(pxList, len+1, idx, end, _);

    UBaseType_t uxListRemove( ListItem_t * const pxItemToRemove ) PRIVILEGED_FUNCTION;
    //@ requires exists<struct xLIST *>(?container) &*& List_t(container, ?len, ?idx, ?end, ?cells) &*& (mem(pxItemToRemove, cells) == true) &*& (pxItemToRemove != end);
    //@ ensures List_t(container, len-1, _, end, remove(pxItemToRemove, cells)) &*& ListItem_t(pxItemToRemove, _, _, _, NULL);
    
/*@
    
lemma void dls_length(
	struct xLIST_ITEM *n,
	struct xLIST_ITEM *nprev,
	struct xLIST_ITEM *mnext,
	struct xLIST_ITEM *m,
	list<struct xLIST_ITEM *> cells)
	requires DLS(n, nprev, mnext, m, cells);
	ensures DLS(n, nprev, mnext, m, cells) &*& length(cells) > 0;
{
	open DLS(n, nprev, mnext, m, cells);
	
	assert cells == cons(n, ?t); 
	switch (t) {
		case nil: 
		
			close DLS(n, nprev, mnext, m, cells);
			
		case cons(h2, t2):
		
			assert DLS(?nnext, n, mnext, m, t);
			dls_length(nnext, n, mnext, m, t);
			close DLS(n, nprev, mnext, m, cells);
	}
}

lemma void dls_star_item(
        struct xLIST_ITEM *n,
        struct xLIST_ITEM *m,
        struct xLIST_ITEM *x)
	requires DLS(n, ?nprev, ?mnext, m, ?cells) &*& ListItem_t(x, ?v, ?xnext, ?xprev, ?l2);
	ensures DLS(n, nprev, mnext, m, cells) &*& ListItem_t(x, v, xnext, xprev, l2) &*& mem(x, cells) == false;
{
        open DLS(n, nprev, mnext, m, cells);
        if (n == m) {
                assert ListItem_t(n, _, _, _, _);
                open ListItem_t(n, _, _, _, _);
                open ListItem_t(x, _, _, _, _);
                assert n != x;
                close ListItem_t(x, _, _, _, _);
                close ListItem_t(n, _, _, _, _);
                close DLS(n, nprev, mnext, m, cells);
        }
        else {
                assert DLS(?nnext, n, mnext, m, tail(cells));
                dls_star_item(nnext, m, x);
                open ListItem_t(n, _, _, _, _);
                open ListItem_t(x, _, _, _, _);
                assert n != x;
                close ListItem_t(x, _, _, _, _);
                close ListItem_t(n, _, _, _, _);
                close DLS(n, nprev, mnext, m, cells);
        }
}
	
lemma void dls_distinct(
	struct xLIST_ITEM *n,
	struct xLIST_ITEM *nprev,
	struct xLIST_ITEM *mnext,
	struct xLIST_ITEM *m,
	list<struct xLIST_ITEM *> cells)
  requires DLS(n, nprev, mnext, m, cells);
  ensures DLS(n, nprev, mnext, m, cells) &*& distinct(cells) == true;
{

	open DLS(n, nprev, mnext, m, cells);
	assert (cells == cons(n, ?t));
	
	switch (t)
	{
		case nil: 
		
			close DLS(n, nprev, mnext, m, cells);
			
		case cons(h2, t2): 
		
			assert DLS(?nnext, n, mnext, m, t);
			dls_distinct(nnext, n, mnext, m, t);
			dls_star_item(nnext, m, n);
			close DLS(n, nprev, mnext, m, cells);
			
	}
}

lemma void singleton_cells(
	struct xLIST_ITEM *n,
	struct xLIST_ITEM *m)
	requires DLS(n, ?nprev, ?mnext, m, ?cells);
	ensures DLS(n, nprev, mnext, m, cells) &*& (cells == cons(n, nil) ? m == n : true);
{
	open DLS(n, nprev, mnext, m, cells);
	
	if (cells == cons(n, nil))
	{
		if (m != n) { open DLS(_, n, mnext, m, nil);}
	}
	
	close DLS(n, nprev, mnext, m, cells);
}

lemma void last_element_in_cells(
	struct xLIST_ITEM *n,
	struct xLIST_ITEM *nprev,
	struct xLIST_ITEM *mnext,
	struct xLIST_ITEM *m,
	list<struct xLIST_ITEM *> cells)
	requires DLS(n, nprev, mnext, m, cells);
	ensures DLS(n, nprev, mnext, m, cells) &*& mem(m, cells) == true;
{

	open DLS(n, nprev, mnext, m, cells);
	assert cells == cons(?h, ?t);
	switch(t)
	{	
		case nil:
			length_nonnegative(t);
			if (m == n) 
			{
			
				close DLS(n, nprev, mnext, m, cons(n,nil));
				
			} else {
			
				assert DLS(?nnext, n, mnext, m, t);
				open DLS(nnext, n, mnext, m, t);	
			}

			
		case cons (h2, t2):

			assert DLS(?nnext, n,  mnext, m, cons(h2, t2));
			last_element_in_cells(nnext, n, mnext, m, t);
			close DLS(n, nprev, mnext, m, cells);
	}

}

lemma void append_dls(
	struct xLIST_ITEM *n,
	struct xLIST_ITEM *nprev,
	struct xLIST_ITEM *mnext, 
	struct xLIST_ITEM *m,
	struct xLIST_ITEM *onext,
	struct xLIST_ITEM *o,
	list<struct xLIST_ITEM *> cells1,
	list<struct xLIST_ITEM *> cells2)
  requires DLS(n, nprev, mnext, m, cells1) &*& DLS(mnext, m, onext, o, cells2);
  ensures DLS(n, nprev, onext, o, append(cells1, cells2));
{
	switch (tail(cells1)) {
		case nil:
		
			singleton_cells(n, m);
			open DLS(n, nprev, mnext, m, cells1);

		
			dls_star_item(mnext, o, n);
			last_element_in_cells(mnext, m, onext, o, cells2);
			close DLS(n, nprev, onext, o, cons(n, cells2));
			
		case cons(h2, t2) : 
			
			open DLS(n, nprev, mnext, m, cells1);
			
			assert DLS(?nnext, n, mnext, m, tail(cells1));
			append_dls(nnext, n, mnext, m, onext, o, tail(cells1), cells2);
			assert DLS(nnext, n, onext, o, append(tail(cells1), cells2));
			
			dls_star_item(nnext, o, n);
			last_element_in_cells(nnext, n, onext, o, append(tail(cells1), cells2));
			
			close DLS(n, nprev, onext, o, cons(n, append(tail(cells1), cells2)));
			
	}
}

lemma void split_dls(
	struct xLIST_ITEM *n, 
	struct xLIST_ITEM *nprev, 
	struct xLIST_ITEM *mnext, 
	struct xLIST_ITEM *m,
	struct xLIST_ITEM *o,
	list<struct xLIST_ITEM *>cells)
  requires DLS(n, nprev, mnext, m, cells) &*& (mem(o, cells) == true) &*& (o != n);
  ensures DLS(n, nprev, o, ?oprev, take(index_of(o,cells),cells)) &*& DLS(o, oprev, mnext, m, cons(o, tail(drop(index_of(o,cells),cells))));
{
	switch(tail(cells))
	{
		case nil:
			open DLS(n, nprev, mnext, m, cells);
			
		case cons(h2, t2):
		
			open DLS(n, nprev, mnext, m, cells);
			
			assert DLS(?nnext, n, mnext, m, tail(cells));
			
			if (nnext == o)
			{
				
				assert ListItem_t(n, _, nnext, nprev, _);
				open DLS(nnext, n, mnext, m, tail(cells));
				assert index_of(o, cells) == 1;
				close DLS(nnext, n, mnext, m, tail(cells));

				close DLS(n, nprev, nnext, n, cons(n, nil));

			} else
			{
			
				split_dls(nnext, n, mnext, m, o, tail(cells));
				
				assert DLS(nnext, n, o, ?oprev, take(index_of(o,tail(cells)),tail(cells)));
				
				dls_star_item(nnext, oprev, n);
				last_element_in_cells(nnext, n, o, oprev, take(index_of(o,tail(cells)),tail(cells)));
				close DLS(n, nprev, o, oprev, cons(n,take(index_of(o,tail(cells)),tail(cells))));
				
				mem_index_of(o, tail(cells));

			}
			
			
	}
}

lemma void remove_item<t>(
	t item,
	list<t> cells)
	requires mem(item, cells) == true;
	ensures remove(item, cells) == append(take(index_of(item, cells), cells), tail(drop(index_of(item, cells), cells)));
{

	switch (cells) 
	{
		case nil : assert false;
		case cons(h, t) : 
			if (h == item) {
			} else {

				mem_index_of(item, t);
				remove_item(item, t);
			}
	}
}

lemma void index_of_nth<t>(
	t item,
	list<t> cells)
	requires mem(item, cells) == true;
	ensures nth(index_of(item, cells), cells) == item;
{

	switch (cells) 
	{
		case nil : assert false;
		case cons(h, t) : 
			if (h == item) {
			} else {

				mem_index_of(item, t);
				index_of_nth(item, t);
			}
	}
}

lemma void idx_member<t>(
	t idx,
	t item,
	list<t> cells)
	requires mem(item, cells) == true &*& mem(idx, cells) == true &*& (item != idx);
	ensures (mem(idx, remove(item, cells)) == true);

{
	mem_index_of(item, cells);
	append_take_drop_n(cells, index_of(item,cells));
	mem_append(idx, take(index_of(item,cells), cells), drop(index_of(item,cells), cells));
	assert ((mem(idx, take(index_of(item,cells),cells)) == true) || (mem(idx, take(index_of(item,cells),cells)) == false));
	switch (drop(index_of(item,cells), cells)){
		case nil: 
			assert (mem(idx, drop(index_of(item,cells), cells)) == false);
			assert (mem(idx, take(index_of(item,cells), cells)) == true);
			
		case cons(x, x0) :
			index_of_nth(item, cells);
			drop_n_plus_one(index_of(item, cells), cells);
			assert (x == item);
			assert (mem(idx, tail(drop(index_of(item,cells),cells))) == true || mem(idx, take(index_of(item,cells),cells)));
	}
	
	remove_item(item, cells);
	mem_append(idx, take(index_of(item,cells), cells), tail(drop(index_of(item,cells), cells)));
}

lemma void mem_drop<t>(
	t idx,
	list<t> cells)
	requires mem(idx, cells) == true;
	ensures head(drop(index_of(idx, cells),cells)) == idx;
{

	mem_index_of(idx,cells);
	index_of_nth(idx, cells);
	drop_n_plus_one(index_of(idx,cells),cells);
}

lemma void join_cells<t>(
	list<t> cells,
	list<t> cells_of_dls1,
	list<t> cells_of_dls2,
	t item)
	requires mem(item, cells) == true &*& cells_of_dls1 == take(index_of(item, cells), cells) &*& cells_of_dls2 == cons(item, tail(drop(index_of(item, cells), cells)));
	ensures (cells == append(cells_of_dls1, cells_of_dls2));
{

	mem_drop(item, cells);
	
	mem_index_of(item, cells);
	drop_n_plus_one(index_of(item,cells),cells);
	assert (drop(index_of(item, cells),cells) != nil);
	
	
	switch (drop(index_of(item,cells),cells)) {
		case nil: assert false;
		case cons(h,t): 
			assert (h == item);
			assert (t == tail(drop(index_of(item,cells),cells)));
		}
	
	assert (cons(item,tail(drop(index_of(item,cells),cells))) == drop(index_of(item,cells),cells));
	
	append_take_drop_n(cells,index_of(item,cells));
}

lemma void head_take<t>(
	t idx,
	list<t> cells)
	requires mem(idx, cells) == true &*& idx != head(cells);
	ensures head(take(index_of(idx,cells),cells)) == head(cells);
{
	
	switch (cells) {
		case nil: assert(false);
		case cons(h, t):
			assert h != idx;
			assert index_of(idx,cells) == 1 + index_of(idx,t);
			mem_index_of(idx,t);
			assert index_of(idx,cells) > 0;
			
	}
	
	length_take(index_of(idx,cells), cells);
	assert (take(index_of(idx,cells),cells) != nil);
	
	switch(take(index_of(idx,cells),cells)) {
		case nil: assert false;
		case cons(h,t): 
			assert h == head(cells);
	}
}

lemma void head_append<t>(
	list<t> cells0,
	list<t> cells1)
	requires true;
	ensures cells0 == nil? head(append(cells0,cells1)) == head(cells1) : head(append(cells0,cells1)) == head(cells0);
{
	switch (cells0) {
		case nil : append_nil(cells0);
		case cons(x, x0) : switch (append(cells0,cells1)) {
			case nil : assert false;
			case cons(y, y0) : y == x;
			};
		}
}

lemma void extract_last_item(
	struct xLIST_ITEM *n,
	struct xLIST_ITEM *m,
	list<struct xLIST_ITEM *> cells)
	requires DLS(n, ?nprev, ?mnext, m, cells) &*& (m != n);
	ensures DLS(n, nprev, m, ?mprev, take(length(cells) - 1, cells)) &*& ListItem_t(m, _, mnext, mprev, _) &*& drop(length(cells)-1, cells) == cons(m, nil);
{

	switch (tail(cells)) {
		case nil:
			
			open DLS(n, nprev, mnext, m, cells);
			close DLS(n, nprev, mnext, m, cons(n, nil));
			singleton_cells(n, m);
			
		case cons(h2, t2) :
		
			
		
			open DLS(n, nprev, mnext, m, cells);
			assert DLS(?nnext, n, mnext, m, tail(cells));
			
			
			if (nnext == m)
			{
				open DLS(nnext, n, mnext, m, tail(cells));
				close DLS(n, nprev, m, n, cons(n, nil));
			} else {
				
				extract_last_item(nnext, m, tail(cells));
				
				assert ListItem_t(m, _, mnext, ?mprev, _);
				assert DLS(nnext, n, m, mprev, ?t);
				
				
				dls_star_item(nnext, mprev, n);
				last_element_in_cells(nnext, n, m, mprev, t);
				
				close DLS(n, nprev, m, mprev, cons(n, t));
				
				assert(cells == cons(?h1, ?t1));
				length_nonnegative(t2);

			} 
	}
}
	
@*/
	