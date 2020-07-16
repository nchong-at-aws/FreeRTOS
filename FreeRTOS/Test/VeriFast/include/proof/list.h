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

/* Empty/no-op macros */
/* Tracing */

#define listFIRST_LIST_ITEM_INTEGRITY_CHECK_VALUE
#define listSECOND_LIST_ITEM_INTEGRITY_CHECK_VALUE
#define listFIRST_LIST_INTEGRITY_CHECK_VALUE
#define listSECOND_LIST_INTEGRITY_CHECK_VALUE
#define configLIST_VOLATILE
#define PRIVILEGED_FUNCTION
#define listSET_FIRST_LIST_ITEM_INTEGRITY_CHECK_VALUE( pxItem )
#define listSET_SECOND_LIST_ITEM_INTEGRITY_CHECK_VALUE( pxItem )
#define listSET_LIST_INTEGRITY_CHECK_1_VALUE( pxList )
#define listSET_LIST_INTEGRITY_CHECK_2_VALUE( pxList )
#define listTEST_LIST_ITEM_INTEGRITY( pxItem )
#define listTEST_LIST_INTEGRITY( pxList )
#define portMAX_DELAY 127

/*
 * Definition of the only type of object that a list can contain.
 */
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

/*
 * Definition of the type of queue used by the scheduler.
 */
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

predicate list_item(
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
           list_item(n, _, mnext, nprev, _)
         : cells == cons(n, ?cells0) &*&
           list_item(n, _, ?o, nprev, _) &*& 
           DLS(o, n, mnext, m, cells0);

predicate list(
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
  
predicate list_uninitialised(struct xLIST *list) = 
    list->uxNumberOfItems |-> _ &*&
    list->pxIndex |-> _ &*&
    list_item(&(list->xListEnd), _, _, _, _);

@*/


void vListInitialise( List_t * const pxList ) PRIVILEGED_FUNCTION;
    //@ requires list_uninitialised(pxList); 
    //@ ensures list(pxList, 0, ?end, end, cons(end,nil));

    void vListInitialiseItem( ListItem_t * const pxItem ) PRIVILEGED_FUNCTION;
    //@ requires list_item(pxItem, ?value, ?next, ?prev, _);
    //@ ensures list_item(pxItem, value, next, prev, NULL);

    void vListInsert( List_t * const pxList,
                      ListItem_t * const pxNewListItem ) PRIVILEGED_FUNCTION;

/*
 * Insert a list item into a list.  The item will be inserted in a position
 * such that it will be the last item within the list returned by multiple
 * calls to listGET_OWNER_OF_NEXT_ENTRY.
 *
 * The list member pxIndex is used to walk through a list.  Calling
 * listGET_OWNER_OF_NEXT_ENTRY increments pxIndex to the next item in the list.
 * Placing an item in a list using vListInsertEnd effectively places the item
 * in the list position pointed to by pxIndex.  This means that every other
 * item within the list will be returned by listGET_OWNER_OF_NEXT_ENTRY before
 * the pxIndex parameter again points to the item being inserted.
 *
 * @param pxList The list into which the item is to be inserted.
 *
 * @param pxNewListItem The list item to be inserted into the list.
 *
 * \page vListInsertEnd vListInsertEnd
 * \ingroup LinkedList
 */
    void vListInsertEnd( List_t * const pxList,
                         ListItem_t * const pxNewListItem ) PRIVILEGED_FUNCTION;

/*
 * Remove an item from a list.  The list item has a pointer to the list that
 * it is in, so only the list item need be passed into the function.
 *
 * @param uxListRemove The item to be removed.  The item will remove itself from
 * the list pointed to by it's pxContainer parameter.
 *
 * @return The number of items that remain in the list after the list item has
 * been removed.
 *
 * \page uxListRemove uxListRemove
 * \ingroup LinkedList
 */
    UBaseType_t uxListRemove( ListItem_t * const pxItemToRemove ) PRIVILEGED_FUNCTION;

    #ifdef __cplusplus
        }
    #endif

#endif /* ifndef LIST_H */