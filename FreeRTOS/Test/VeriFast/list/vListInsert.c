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

#include "proof/list.h"

#ifdef VERIFAST /* choose function */
ListItem_t * choose(List_t * list);
    //@ requires DLS(&(list->xListEnd), ?endprev, &(list->xListEnd), endprev, ?cells);
    //@ ensures DLS(&(list->xListEnd), endprev, &(list->xListEnd), endprev, cells) &*& mem(result, cells) == true;
#endif

void vListInsert( List_t * const pxList,
                  ListItem_t * const pxNewListItem )
    //@ requires List_t(pxList, ?len, ?idx, ?end, ?cells) &*& ListItem_t(pxNewListItem, ?val, _, _, _) &*& (mem(pxNewListItem, cells) == false);
    //@ ensures List_t(pxList, len+1, idx, end, ?newcells) &*& (remove(pxNewListItem, newcells) == cells);
{
    ListItem_t * pxIterator;
    
    //@ open ListItem_t(pxNewListItem, _, _, _, _);
    
    const TickType_t xValueOfInsertion = pxNewListItem->xItemValue;

    //@ open List_t(pxList, len, idx, end, cells);
    //@ assert DLS(end, ?endprev, end, endprev, cells);
    //@ index_of_last_in_DLS(end, endprev, cells);

    listTEST_LIST_INTEGRITY( pxList );
    listTEST_LIST_ITEM_INTEGRITY( pxNewListItem );

    if( xValueOfInsertion == portMAX_DELAY )
    {
        //@ open DLS(end, endprev, end, endprev, cells);
    
        /*@
       
        if (end == endprev)
        {
            open ListItem_t(end, _, end, end, _);
            
        } else
        {
            open ListItem_t(end, _, ?endnext, endprev, _);
            DLS_length_positive(endnext, endprev);
            
            if (endnext == endprev)
            {
                open DLS(endprev, _, _, endprev, _);
                
            } else 
            {
                DLS_extract_last_item(endnext, endprev, tail(cells));
            }
        
        open ListItem_t(endprev, _, end, _, _);
            
        }
        @*/
    
        pxIterator = pxList->xListEnd.pxPrevious;
    }
    else
    {
        
#ifdef VERIFAST /* overapproximate loop */    
        pxIterator = choose(pxList);
#else
        for( pxIterator = ( ListItem_t * ) &( pxList->xListEnd ); pxIterator->pxNext->xItemValue <= xValueOfInsertion; pxIterator = pxIterator->pxNext ) 
        {
        }
#endif

        //@ assert mem(pxIterator, cells) == true;
        
        /*@
        
        if(pxIterator == end)
        {
            open DLS(end, endprev, end, endprev, cells);
            open ListItem_t(end, _, ?endnext, endprev, _);
            
            if (end != endprev)
            {
                open DLS(endnext, end, end, endprev, tail(cells));
                open ListItem_t(endnext, _, _, end, _); 
            }

        } else
        {

            split_DLS(end, endprev, end, endprev, pxIterator, cells);
            assert DLS(end, endprev, pxIterator, ?iterprev, ?cells1);
            assert DLS(pxIterator, iterprev, end, endprev, ?cells2);
            open DLS(pxIterator, iterprev, end, endprev, cells2);
            open ListItem_t(pxIterator, _, ?iternext, iterprev, _);
            
            if (pxIterator == endprev)
            {
                open DLS(end, endprev, pxIterator, iterprev, cells1);
                open ListItem_t(iternext, _, _, pxIterator, _); 
                
            } else
            {
                open DLS(iternext, pxIterator, end, endprev, tail(cells2));
                open ListItem_t(iternext, _, _, pxIterator, _);
            }
        }
        @*/

    }

    pxNewListItem->pxNext = pxIterator->pxNext;
    pxNewListItem->pxNext->pxPrevious = pxNewListItem;
    pxNewListItem->pxPrevious = pxIterator;
    pxIterator->pxNext = pxNewListItem;

    pxNewListItem->pxContainer = pxList;

    ( pxList->uxNumberOfItems )++;
    
    //@ close ListItem_t(pxNewListItem, _, ?iternext, pxIterator, _);
    //@ close ListItem_t(pxIterator, _, pxNewListItem, ?iterprev, _);
    
    /*@
    
    if (xValueOfInsertion == portMAX_DELAY)
    {
    
        if (end == endprev)
        {
           close DLS(pxNewListItem, end, end, pxNewListItem, cons(pxNewListItem, nil));
           close DLS(end, pxNewListItem, end, pxNewListItem, cons(end, cons(pxNewListItem,nil)));
           close List_t(pxList, len+1, idx, end, cons(end, cons(pxNewListItem, nil)));
           
        } else
        {
         
           close ListItem_t(end, _, ?endnext, pxNewListItem, _);
           close DLS(pxNewListItem, endprev, end, pxNewListItem, cons(pxNewListItem, nil));
           close DLS(endprev, iterprev, end, pxNewListItem, cons(endprev, cons(pxNewListItem, nil)));
           
           if (endnext == endprev)
           {
               close DLS(iterprev, pxNewListItem, end, pxNewListItem, cons(iterprev, cons(endprev, cons(pxNewListItem, nil))));
               close List_t(pxList, len+1, idx, end, cons(iterprev, cons(endprev, cons(pxNewListItem, nil))));

           } else
           {
               assert DLS(endnext, end, endprev, iterprev, ?cells0);
               append_DLS(endnext, end, endprev, iterprev, end, pxNewListItem, cells0, cons(endprev, cons(pxNewListItem, nil)));
               close DLS(end, pxNewListItem, end, pxNewListItem, cons(end, append(cells0, cons(endprev, cons(pxNewListItem, nil)))));
               append_take_drop_n(cells, length(cells) - 1);
               append_assoc(cons(end, cells0), cons(endprev, nil), cons(pxNewListItem, nil));
               remove_append(pxNewListItem, cells, cons(pxNewListItem, nil));
               close List_t(pxList, len+1, idx, end, append(cells, cons(pxNewListItem, nil)));  
           }
        }
    
    } else
    {
    
        if (pxIterator == end)
        {
        
            if (iternext == end)
            {
                close DLS(pxNewListItem, pxIterator, end, pxNewListItem, cons(pxNewListItem,nil));
                close DLS(end, pxNewListItem, end, pxNewListItem, cons(end,cons(pxNewListItem,nil)));
                close List_t(pxList, len+1, idx, end, cons(end, cons(pxNewListItem, nil)));
        
            } else
            {
                close ListItem_t(iternext, _, _, pxNewListItem, _);
            
                if (iternext == endprev)
                {
                    close DLS(iternext, pxNewListItem, end, endprev, cons(iternext, nil));
                    last_element_in_DLS(iternext, endprev, cons(iternext, nil));
                
                } else
                {
                    assert DLS(_, iternext, end, endprev, ?cells2);
                    close DLS(iternext, pxNewListItem, end, endprev, cons(iternext,cells2));
                    last_element_in_DLS(iternext, endprev, cons(iternext, cells2));
                
                }
            
                assert DLS(iternext, pxNewListItem, end, endprev, ?cells2);
                DLS_star_item(iternext, endprev, pxNewListItem);
                
                close DLS(pxNewListItem, pxIterator, end, endprev, cons(pxNewListItem, cells2));
                close DLS(end, endprev, end, endprev, cons(end, cons(pxNewListItem, cells2)));
                close List_t(pxList, len+1, idx, end, cons(end, cons(pxNewListItem, cells2)));
            
            }
           
        
        } else
        {
        
            if (pxIterator == endprev)
            {
                close ListItem_t(iternext, _, ?o, pxNewListItem, _);
            
                if (iterprev == end)
                {
                    close DLS(end, pxNewListItem, pxIterator, end, cons(end, nil));
                
                } else
                {
                    assert DLS(_, iternext, pxIterator, iterprev, ?cells1);
                    close DLS(end, pxNewListItem, pxIterator, iterprev, cons(end, cells1));
                    assert (cons(end, cells1) == take(index_of(pxIterator, cells), cells));
                }
            
                assert DLS(end, pxNewListItem, pxIterator, iterprev, ?cells1);
                close DLS(pxNewListItem, pxIterator, iternext, pxNewListItem, cons(pxNewListItem, nil));
                close DLS(pxIterator, iterprev, iternext, pxNewListItem, cons(pxIterator, cons(pxNewListItem, nil)));
                append_DLS(end, pxNewListItem, pxIterator, iterprev, iternext, pxNewListItem, cells1, cons(pxIterator,cons(pxNewListItem,nil)));
                assert (index_of(endprev, cells) == length(cells) - 1);
                assert (drop(index_of(pxIterator, cells) + 1, cells) == nil);
                drop_n_plus_one(index_of(pxIterator, cells), cells);
                index_of_nth(pxIterator, cells);
                append_take_drop_n(cells, index_of(pxIterator, cells));
                remove_append(pxNewListItem, cells1, cons(pxIterator, cons(pxNewListItem, nil)));
                close List_t(pxList, len+1, idx, end, append(cells1, cons(pxIterator,cons(pxNewListItem,nil))));  
         
            } else
            {
                close ListItem_t(iternext, _, _, pxNewListItem, _);
            
                if (iternext == endprev)
                {
                    close DLS(iternext, pxNewListItem, end, endprev, cons(iternext, nil));
                
                } else
                {
                    assert DLS(_, iternext, end, endprev, ?cells2);
                    close DLS(iternext, pxNewListItem, end, endprev, cons(iternext, cells2));
                } 
            
                assert DLS(end, endprev, pxIterator, iterprev, ?cells1);
                DLS_length_positive(end, iterprev);
                head_take(pxIterator, cells);
                assert DLS(iternext, pxNewListItem, end, endprev, ?cells2);
                last_element_in_DLS(iternext, endprev, cells2);
                DLS_star_item(iternext, endprev, pxNewListItem);
                close DLS(pxNewListItem, pxIterator, end, endprev, cons(pxNewListItem, cells2));
                close DLS(pxIterator, iterprev, end, endprev, cons(pxIterator, cons(pxNewListItem, cells2)));  
                append_DLS(end, endprev, pxIterator, iterprev, end, endprev, cells1, cons(pxIterator, cons(pxNewListItem, cells2)));
                head_append(cells1, cons(pxIterator, cons(pxNewListItem, cells2)));   
                drop_n_plus_one(index_of(pxIterator, cells), cells);
                index_of_nth(pxIterator, cells);
                append_take_drop_n(cells, index_of(pxIterator, cells));
                remove_append(pxNewListItem, cells1, cons(pxIterator, cons(pxNewListItem, cells2)));
                close List_t(pxList, len+1, idx, end, append(cells1, cons(pxIterator, cons(pxNewListItem, cells2))));   
            }
        }       
    }
    
    @*/
}