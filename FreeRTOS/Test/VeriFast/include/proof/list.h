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
#include <string.h>

typedef int TickType_t;
typedef int UBaseType_t;
typedef int BaseType_t;

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

struct xLIST;
struct xLIST_ITEM
{
    listFIRST_LIST_ITEM_INTEGRITY_CHECK_VALUE
    configLIST_VOLATILE TickType_t xItemValue;
    struct xLIST_ITEM * configLIST_VOLATILE pxNext;
    struct xLIST_ITEM * configLIST_VOLATILE pxPrevious;
    void * pvOwner;
    struct xLIST * configLIST_VOLATILE pxContainer;
    listSECOND_LIST_ITEM_INTEGRITY_CHECK_VALUE
};
typedef struct xLIST_ITEM ListItem_t;

struct xMINI_LIST_ITEM
{
    listFIRST_LIST_ITEM_INTEGRITY_CHECK_VALUE
    configLIST_VOLATILE TickType_t xItemValue;
    struct xLIST_ITEM * configLIST_VOLATILE pxNext;
    struct xLIST_ITEM * configLIST_VOLATILE pxPrevious;
};
typedef struct xMINI_LIST_ITEM MiniListItem_t;

typedef struct xLIST
{
    listFIRST_LIST_INTEGRITY_CHECK_VALUE 
    volatile UBaseType_t uxNumberOfItems;
    ListItem_t * configLIST_VOLATILE pxIndex;
#ifdef VERIFAST
        ListItem_t xListEnd;
#else
        MiniListItem_t xListEnd;
#endif
        listSECOND_LIST_INTEGRITY_CHECK_VALUE
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
    List_t * const pxConstList = ( pxList );                                               \                        \
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
  ListItem_t *n,
  TickType_t val,
  ListItem_t *next,
  ListItem_t *prev,
  List_t *container) =
  n->xItemValue |-> val &*&
  n->pxNext |-> next &*&
  n->pxPrevious |-> prev &*&
  n->pxContainer |-> container;

predicate DLS(
  ListItem_t *n,
  ListItem_t *nprev,
  ListItem_t *mnext,
  ListItem_t *m,
  list<struct xLIST_ITEM *> cells,
  List_t *container) =
  n == m ? cells == cons(n, nil) &*&
           ListItem_t(n, _, mnext, nprev, container)
         : cells == cons(n, ?cells0) &*&
           ListItem_t(n, _, ?o, nprev, container) &*& 
           DLS(o, n, mnext, m, cells0, container);

predicate List_t(
  List_t *l,
  int len,
  ListItem_t *idx,
  ListItem_t *end,
  list<ListItem_t *>cells) =
  l->uxNumberOfItems |-> len &*&
  l->pxIndex |-> idx &*&
  end == &(l->xListEnd) &*&
  end == head(cells) &*&
  len + 1 == length(cells) &*&
  mem(idx, cells) == true &*&
  DLS(end, ?m, end, m, cells, l);
  
predicate List_t_uninitialised(List_t *list) = 
    list->uxNumberOfItems |-> _ &*&
    list->pxIndex |-> _ &*&
    ListItem_t(&(list->xListEnd), _, _, _, list);

@*/


void vListInitialise( List_t * const pxList ) PRIVILEGED_FUNCTION;

void vListInitialiseItem( ListItem_t * const pxItem ) PRIVILEGED_FUNCTION;

void vListInsert( List_t * const pxList, ListItem_t * const pxNewListItem ) PRIVILEGED_FUNCTION;

void vListInsertEnd( List_t * const pxList, ListItem_t * const pxNewListItem ) PRIVILEGED_FUNCTION;

UBaseType_t uxListRemove( ListItem_t * const pxItemToRemove ) PRIVILEGED_FUNCTION;

/*@
    
lemma void DLS_length_positive(
	ListItem_t *n,
	ListItem_t *m)
	requires DLS(n, ?nprev, ?mnext, m, ?cells, ?container);
	ensures DLS(n, nprev, mnext, m, cells, container) &*& length(cells) > 0;
{
	open DLS(n, nprev, mnext, m, cells, _);
	
	assert cells == cons(n, ?t); 
	switch (t) {
		case nil: 
		
			close DLS(n, nprev, mnext, m, cells, _);
			
		case cons(h2, t2):
		
			assert DLS(?nnext, n, mnext, m, t, _);
			DLS_length_positive(nnext, m);
			close DLS(n, nprev, mnext, m, cells, _);
	}
}

lemma void DLS_star_item(
        ListItem_t *n,
        ListItem_t *m,
        ListItem_t *x)
	requires DLS(n, ?nprev, ?mnext, m, ?cells, ?container) &*& ListItem_t(x, ?v, ?xnext, ?xprev, ?l2);
	ensures DLS(n, nprev, mnext, m, cells, container) &*& ListItem_t(x, v, xnext, xprev, l2) &*& mem(x, cells) == false;
{
        open DLS(n, nprev, mnext, m, cells, _);
        if (n == m) {
                assert ListItem_t(n, _, _, _, _);
                open ListItem_t(n, _, _, _, _);
                open ListItem_t(x, _, _, _, _);
                assert n != x;
                close ListItem_t(x, _, _, _, _);
                close ListItem_t(n, _, _, _, _);
                close DLS(n, nprev, mnext, m, cells, _);
        }
        else {
                assert DLS(?nnext, n, mnext, m, tail(cells), _);
                DLS_star_item(nnext, m, x);
                open ListItem_t(n, _, _, _, _);
                open ListItem_t(x, _, _, _, _);
                assert n != x;
                close ListItem_t(x, _, _, _, _);
                close ListItem_t(n, _, _, _, _);
                close DLS(n, nprev, mnext, m, cells, _);
        }
}
	
lemma void DLS_distinct(
	ListItem_t *n,
	ListItem_t *nprev,
	ListItem_t *mnext,
	ListItem_t *m,
	list<ListItem_t *> cells)
  requires DLS(n, nprev, mnext, m, cells, ?container);
  ensures DLS(n, nprev, mnext, m, cells, container) &*& distinct(cells) == true;
{

	open DLS(n, nprev, mnext, m, cells, _);
	
	switch (tail(cells))
	{
		case nil: 
		
			close DLS(n, nprev, mnext, m, cells, _);
			
		case cons(h2, t2): 
		
			assert DLS(?nnext, n, mnext, m, tail(cells), _);
			DLS_distinct(nnext, n, mnext, m, tail(cells));
			DLS_star_item(nnext, m, n);
			close DLS(n, nprev, mnext, m, cells, _);
			
	}
}

lemma void singleton_DLS(
	ListItem_t *n,
	ListItem_t *m)
	requires DLS(n, ?nprev, ?mnext, m, ?cells, ?container);
	ensures DLS(n, nprev, mnext, m, cells, container) &*& (cells == cons(n, nil) ? m == n : true);
{
	open DLS(n, nprev, mnext, m, cells, _);
	
	if (cells == cons(n, nil))
	{
		if (m != n) { open DLS(_, n, mnext, m, nil, _);}
	}
	
	close DLS(n, nprev, mnext, m, cells, _);
}

lemma void last_element_in_DLS(
	ListItem_t *n,
	ListItem_t *m,
	list<ListItem_t *> cells)
	requires DLS(n, ?nprev, ?mnext, m, cells, ?container);
	ensures DLS(n, nprev, mnext, m, cells, container) &*& mem(m, cells) == true;
{

	open DLS(n, nprev, mnext, m, cells, _);
	assert cells == cons(?h, ?t);
	switch(t)
	{	
		case nil:
			length_nonnegative(t);
			if (m == n) 
			{
			
				close DLS(n, nprev, mnext, m, cons(n,nil), _);
				
			} else {
			
				assert DLS(?nnext, n, mnext, m, t, _);
				open DLS(nnext, n, mnext, m, t, _);	
			}

			
		case cons (h2, t2):

			assert DLS(?nnext, n,  mnext, m, cons(h2, t2), _);
			last_element_in_DLS(nnext, m, t);
			close DLS(n, nprev, mnext, m, cells, _);
	}

}

lemma void append_DLS(
	ListItem_t *n,
	ListItem_t *nprev,
	ListItem_t *mnext, 
	ListItem_t *m,
	ListItem_t *onext,
	ListItem_t *o,
	list<ListItem_t *> cells1,
	list<ListItem_t *> cells2)
  requires DLS(n, nprev, mnext, m, cells1, ?container) &*& DLS(mnext, m, onext, o, cells2, container);
  ensures DLS(n, nprev, onext, o, append(cells1, cells2), container);
{
	switch (tail(cells1)) {
		case nil:
		
			singleton_DLS(n, m);
			open DLS(n, nprev, mnext, m, cells1, _);

		
			DLS_star_item(mnext, o, n);
			last_element_in_DLS(mnext, o, cells2);
			close DLS(n, nprev, onext, o, cons(n, cells2), _);
			
		case cons(h2, t2) : 
			
			open DLS(n, nprev, mnext, m, cells1, _);
			
			assert DLS(?nnext, n, mnext, m, tail(cells1), _);
			append_DLS(nnext, n, mnext, m, onext, o, tail(cells1), cells2);
			assert DLS(nnext, n, onext, o, append(tail(cells1), cells2), _);
			
			DLS_star_item(nnext, o, n);
			last_element_in_DLS(nnext, o, append(tail(cells1), cells2));
			
			close DLS(n, nprev, onext, o, cons(n, append(tail(cells1), cells2)), _);
			
	}
}

lemma void split_DLS(
	ListItem_t *n, 
	ListItem_t *nprev, 
	ListItem_t *mnext, 
	ListItem_t *m,
	ListItem_t *o,
	list<ListItem_t *>cells)
  requires DLS(n, nprev, mnext, m, cells, ?container) &*& (mem(o, cells) == true) &*& (o != n);
  ensures DLS(n, nprev, o, ?oprev, take(index_of(o,cells),cells), container) &*& DLS(o, oprev, mnext, m, cons(o, tail(drop(index_of(o,cells),cells))), container);
{
	switch(tail(cells))
	{
		case nil:
			open DLS(n, nprev, mnext, m, cells, _);
			
		case cons(h2, t2):
		
			open DLS(n, nprev, mnext, m, cells, _);
			
			assert DLS(?nnext, n, mnext, m, tail(cells), _);
			
			if (nnext == o)
			{
				
				open DLS(nnext, n, mnext, m, tail(cells), _);
				close DLS(nnext, n, mnext, m, tail(cells), _);
				close DLS(n, nprev, nnext, n, cons(n, nil), _);

			} else
			{
			
				split_DLS(nnext, n, mnext, m, o, tail(cells));
				
				assert DLS(nnext, n, o, ?oprev, take(index_of(o,tail(cells)),tail(cells)), _);
				
				DLS_star_item(nnext, oprev, n);
				last_element_in_DLS(nnext, oprev, take(index_of(o,tail(cells)),tail(cells)));
				close DLS(n, nprev, o, oprev, cons(n,take(index_of(o,tail(cells)),tail(cells))), _);
				
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

lemma void remove_member<t>(
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

lemma void DLS_extract_last_item(
	ListItem_t *n,
	ListItem_t *m,
	list<ListItem_t *> cells)
	requires DLS(n, ?nprev, ?mnext, m, cells, ?container) &*& (m != n);
	ensures DLS(n, nprev, m, ?mprev, take(length(cells) - 1, cells), container) &*& ListItem_t(m, _, mnext, mprev, container) &*& drop(length(cells)-1, cells) == cons(m, nil);
{

	switch (tail(cells)) {
		case nil:
			
			open DLS(n, nprev, mnext, m, cells, _);
			close DLS(n, nprev, mnext, m, cons(n, nil), _);
			singleton_DLS(n, m);
			
		case cons(h2, t2) :
		
			
		
			open DLS(n, nprev, mnext, m, cells, _);
			assert DLS(?nnext, n, mnext, m, tail(cells), _);
			
			
			if (nnext == m)
			{
				open DLS(nnext, n, mnext, m, tail(cells), _);
				close DLS(n, nprev, m, n, cons(n, nil), _);
			} else {
				
				DLS_extract_last_item(nnext, m, tail(cells));
				assert DLS(nnext, n, m, ?mprev, ?t, _);
				DLS_star_item(nnext, mprev, n);
				last_element_in_DLS(nnext, mprev, t);
				close DLS(n, nprev, m, mprev, cons(n, t), _);
				length_nonnegative(t2);

			} 
	}
}

lemma void remove_append<t>(t x, list<t> l1, list<t> l2)
    requires mem(x, l1) == false;
    ensures remove(x, append(l1, l2)) == append(l1, remove(x, l2));
{
    switch(l1) {
    
        case nil: 
        
        case cons(h1, t1): remove_append(x, t1, l2);
    }
    
}

lemma void index_of_last_in_DLS(ListItem_t *n, ListItem_t *m, list<ListItem_t *> cells)
    requires DLS(n, ?nprev, ?mnext, m, cells, ?container);
    ensures DLS(n, nprev, mnext, m, cells, container) &*& index_of(m, cells) == length(cells) - 1;
{

    switch (tail(cells)){
    
        case nil: 
            
            singleton_DLS(n, m);
            open DLS(n, nprev, mnext, m, cells, _);
            close DLS(n, nprev, mnext, m, cells, _);
        
        case cons(h, t): 
        
            open DLS(n, nprev, mnext, m, cells, _);
            assert DLS(?nnext, n, mnext, m, tail(cells), _);
            index_of_last_in_DLS(nnext, m, tail(cells));   
            close DLS(n, nprev, mnext, m, cells, _);
    }
}
	
@*/